#!/usr/bin/env python3
"""Beat the Blast

Find your way out of a maze before the bomb explodes. Reach any green flag
before time runs out, and avoid unnecessary steps, which can also trigger
an explosion.

Press Start to begin. Drag the yellow player or use the arrow keys or WASD
to move. Pause stops the countdown and hides the maze until you resume.

Pass ten mazes and earn enough points to unlock the next level.
There are 100 levels to complete.
"""

import asyncio
import doctest
from array import array
import math
import os
import random
import sys
import time
import unittest
from collections import deque
from unittest.mock import patch

os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")

# Only the test command uses an offscreen display and silent audio.
if "--test" in sys.argv[1:]:
    os.environ["SDL_VIDEODRIVER"] = "dummy"
    os.environ["SDL_AUDIODRIVER"] = "dummy"

try:
    import pygame
except ModuleNotFoundError:
    pygame = None



# ----------------------------------------------------------------------
# SETTINGS
# ----------------------------------------------------------------------
# Game rules, level sizes, display colors, and movement directions.

STEP_ALLOWANCE = 1.20
LOCK_AFTER_FAILURES = 3
PERFECT_BONUS = 250
BOMB_PLANNING_SECONDS = 30
BOMB_SECONDS_PER_STEP = 0.5
MIN_BOMB_SECONDS = 45
TIMEOUT_PENALTY = 100
RESTART_PENALTY = 100
MAZES_PER_LEVEL = 10
LEVEL_POINTS_REQUIRED = 5000
LEVELS = [(29 + 2 * (level // 5), 21 + 2 * (level // 7), 20 + level // 3)
          for level in range(100)]
DIRECTIONS = [(1, 0), (-1, 0), (0, 1), (0, -1)]
WINDOW_WIDTH = 960
WINDOW_HEIGHT = 720    # short enough to fit a laptop screen with the menu bar and Dock

# Cartoon comic colors.
SKY = (88, 184, 245)
SKY_DOTS = (128, 202, 248)
INK = (27, 27, 27)
WHITE = (255, 255, 255)
PAPER = (255, 246, 223)
YELLOW = (255, 210, 63)
WALL_ORANGE = (240, 124, 58)
RED = (232, 54, 43)
GREEN = (60, 207, 90)
DARK_GREEN = (30, 140, 60)
SPARK_ORANGE = (255, 138, 31)
FUSE_BROWN = (138, 90, 43)
MUTED = (74, 74, 74)
LIGHT_GREY = (226, 226, 226)
LOST_GREY = (190, 190, 190)
CHECKED_YELLOW = (255, 228, 150)
DISABLED_FILL = (150, 205, 240)
DISABLED_TEXT = (60, 118, 160)

# Font files live in the fonts folder next to this file.
FONT_FOLDER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fonts")
COMIC_FONT = "Bangers-Regular.ttf"
TEXT_FONT = "Nunito.ttf"

# Screen areas: the left column of cards, the board, and the bottom row of buttons.
CARD_LEFT = 30
CARD_WIDTH = 230
BOARD_RECT = (286, 84, 644, 528)
MAZE_AREA = (306, 100, 604, 452)
SAMPLE_AREA = (306, 136, 604, 416)    # below the "BFS SEARCH" label
BOTTOM_ROW = 636
BOTTOM_HEIGHT = 54

HELP_LINES = ["Press START, then reach a green flag before the bomb goes off.",
              "Move with the arrow keys, WASD, the arrow buttons, or by dragging or tapping.",
              "Every step counts. Run out of steps and the bomb goes off too.",
              "Take a shortest route for a +250 bonus.",
              "Pass 10 mazes and earn 5,000 points to unlock the next level.",
              "PAUSE hides the maze and freezes the countdown. Press M to mute."]
TIPS = ["Pause hides the maze and freezes the countdown.",
        "The steps bar turns orange when you are close to the step limit.",
        "Take a shortest route for a +250 bonus.",
        "Unlock the next level: pass 10 mazes and earn 5,000 net level points.",
        "Restarting a live attempt costs 100 points and counts as a failure.",
        "Three failures in a row send you back to the previous level.",
        "Press M or the sound button to mute."]


# ----------------------------------------------------------------------
# BUTTON DESCRIPTIONS
# ----------------------------------------------------------------------
# A Button describes a control. Drawing paints it; App handles its action.

class Button:
    """Keep a button's appearance, action, and availability together."""

    def __init__(self, *, label, rect, action, value=0, enabled=True, icon=None):
        """Store a button's label, area, action, and whether it can be clicked.

        An icon name such as "left" or "sound_on" draws a picture instead of the label.

        >>> button = Button(label="New attempt", rect=None, action="retry")
        >>> button.label, button.action, button.enabled
        ('New attempt', 'retry', True)
        """
        self.label = label
        self.rect = rect
        self.action = action
        self.value = value
        self.enabled = enabled
        self.icon = icon


# ----------------------------------------------------------------------
# COUNTDOWN AND POINTS
# ----------------------------------------------------------------------
# Small calculations for time and points, with runnable examples.

def bomb_duration(shortest_distance):
    """Return countdown seconds for a positive shortest-route distance.

    Allow 30 seconds to plan and half a second per shortest-route step, with at
    least 45 seconds overall. This is a starting estimate for playtesting;
    route length alone does not capture how hard a maze is to read.

    >>> bomb_duration(10)
    45
    >>> bomb_duration(60)
    60
    >>> bomb_duration(61)
    61
    """
    estimate = BOMB_PLANNING_SECONDS + shortest_distance * BOMB_SECONDS_PER_STEP
    return max(MIN_BOMB_SECONDS, math.ceil(estimate))


def escape_points(shortest_distance, steps, seconds_left, bomb_seconds):
    """Return escape points before the perfect-route bonus.

    Squaring route efficiency makes extra steps reduce the reward more strongly
    than a proportional score would. More time left also earns more points.
    Steps, shortest_distance, and bomb_seconds must be positive; seconds_left
    must be between zero and bomb_seconds.

    >>> escape_points(10, 10, 30, 60)
    625
    >>> escape_points(10, 10, 60, 60)
    1000
    >>> escape_points(10, 12, 30, 60)
    434
    """
    efficiency = shortest_distance / steps
    time_factor = 0.25 + 0.75 * seconds_left / bomb_seconds
    return max(1, round(1000 * efficiency ** 2 * time_factor))


def step_penalty(steps, step_limit, shortest_distance):
    """Return the positive point cost of going over the step limit.

    Extra steps cost more relative to a short maze than a long one. The minimum
    cost is 25 points. Call when steps > step_limit and shortest_distance > 0;
    Game subtracts the result from the score.

    >>> step_penalty(13, 12, 10)
    25
    >>> step_penalty(20, 12, 10)
    80
    """
    over_limit = steps - step_limit
    return max(25, round(100 * over_limit / shortest_distance))


# ----------------------------------------------------------------------
# MAZE GENERATION AND SEARCHES
# ----------------------------------------------------------------------
# DFS creates paths. BFS measures walking distances. Exit choices are compared
# to favor layouts that take some thought to read.

def exit_distance(candidate):
    """Return the distance from a (position, side, distance) exit candidate.

    >>> exit_distance(((3, 0), 0, 24))
    24
    """
    return candidate[2]


class Maze:
    """Own the maze layout and the checks needed by the game rules."""

    def __init__(self, level, previous_layout=None):
        """Generate a maze for a zero-based level index.

        Maze(0), for example, uses a 29 by 21 grid. previous_layout is a wall pattern
        to avoid repeating when generating a new maze for the same level.
        """
        self.width, self.height, self.extra_openings = LEVELS[level]
        self.minimum_distance = (self.width + self.height) // 2 + level // 2
        self.cleared = False
        self.start = None
        self.exits = set()
        self.grid = []
        self.shortest_distance = 0
        self.generate(previous_layout)

    def is_open(self, x, y):
        """Return True for an open cell, or False for a wall or a cell outside the grid."""
        if x < 0 or x >= self.width or y < 0 or y >= self.height:
            return False
        return self.grid[y][x] == 0

    def get_wall_pattern(self):
        """Return the walls as tuples so two maze layouts can be compared."""
        return tuple(tuple(row) for row in self.grid)

    def create_paths(self):
        """Create connected paths using depth-first search (DFS).

        The stack holds the current branch. Open a path to an unused cell when
        possible; otherwise step back along the branch. Openings connect cells two
        spaces apart, leaving room for walls between neighboring paths.
        """
        self.grid = [[1] * self.width for _ in range(self.height)]
        self.grid[1][1] = 0
        stack = [(1, 1)]
        while stack:
            neighbor = self.open_next_cell(stack[-1])
            if neighbor is None:
                stack.pop()
            else:
                stack.append(neighbor)

    def open_next_cell(self, position):
        """Open a path to a random unused neighbor and return its position.

        Check two cells away to leave walls between parallel paths. Opening right
        from (1, 1), for example, opens (2, 1) and (3, 1), then returns (3, 1).
        Return None when no unused neighbor is available.
        """
        x, y = position
        directions = DIRECTIONS.copy()
        random.shuffle(directions)
        for dx, dy in directions:
            next_x, next_y = x + 2 * dx, y + 2 * dy
            inside = 0 < next_x < self.width - 1 and 0 < next_y < self.height - 1
            if inside and self.grid[next_y][next_x] == 1:
                self.grid[y + dy][x + dx] = 0
                self.grid[next_y][next_x] = 0
                return next_x, next_y
        return None

    def add_connecting_paths(self):
        """Remove some walls between existing paths to create alternative routes.

        DFS alone creates a maze without loops. These connections let players
        choose between routes. extra_openings controls how many walls are removed.
        """
        candidates = []
        for y in range(1, self.height - 1):
            for x in range(1, self.width - 1):
                if self.grid[y][x] == 0:
                    continue
                horizontal = self.is_open(x - 1, y) and self.is_open(x + 1, y)
                vertical = self.is_open(x, y - 1) and self.is_open(x, y + 1)
                if horizontal != vertical:
                    candidates.append((x, y))
        random.shuffle(candidates)
        for x, y in candidates[:self.extra_openings]:
            self.grid[y][x] = 0

    def find_shortest_distance(self):
        """Return the fewest moves to any exit using breadth-first search (BFS).

        BFS checks cells one move away, then two moves away, and so on. Since each
        move costs one step, the first exit reached has the shortest distance.
        Raise ValueError if no exit is reachable. Only the distance is returned.

        Example: If exits are 8, 12, and 15 moves away, return 8.
        """
        queue = deque([(self.start, 0)])
        checked_cells = {self.start}
        while queue:
            (x, y), distance = queue.popleft()
            if (x, y) in self.exits:
                return distance
            for dx, dy in DIRECTIONS:
                neighbor = (x + dx, y + dy)
                if self.is_open(*neighbor) and neighbor not in checked_cells:
                    checked_cells.add(neighbor)
                    queue.append((neighbor, distance + 1))
        raise ValueError("No exit can be reached.")

    def generate(self, previous_layout):
        """Choose a fresh layout and measure its shortest exit distance with BFS."""
        self.grid, self.start, self.exits = self.choose_maze(previous_layout)
        self.shortest_distance = self.find_shortest_distance()

    def choose_maze(self, previous_layout):
        """Return a fresh (grid, start, exits) layout that fits the level reasonably well.

        Try up to 60 mazes, rejecting the previous wall pattern. Prefer a long enough
        route to the nearest exit and exit choices that are less obvious by sight.
        Keep the best result found; this does not guarantee equal difficulty.
        Raise RuntimeError if no fresh layout is found.
        """
        minimum = self.minimum_distance
        best_layout = None
        best_gap = float("inf")
        for attempt in range(60):
            self.create_possible_maze()
            if self.get_wall_pattern() == previous_layout:
                continue
            gap = max(minimum - self.find_shortest_distance(), 0) + self.exit_choice_penalty
            if gap < best_gap:
                best_gap = gap
                grid_copy = [row.copy() for row in self.grid]
                best_layout = (grid_copy, self.start, self.exits.copy())
            if gap == 0:
                break
        if best_layout is None:
            raise RuntimeError("Could not generate a fresh maze.")
        return best_layout

    def create_possible_maze(self):
        """Build one maze to consider: paths, extra connections, a start, and exits."""
        self.create_paths()
        self.add_connecting_paths()
        self.choose_start()
        self.open_exits()

    def open_exits(self):
        """Choose boundary exits and open their cells.

        Store the exit comparison score in exit_choice_penalty so choose_maze()
        can compare complete layouts. This is where that attribute is first set.
        """
        distances = self.distances_from_start()
        candidates = self.exit_candidates(distances)
        first_steps = self.first_steps_from_start()
        selected, self.exit_choice_penalty = self.choose_exit_group(candidates, first_steps)
        self.exits = set()
        for position, side, distance in selected:
            self.exits.add(position)
            x, y = position
            self.grid[y][x] = 0

    def choose_exit_group(self, candidates, first_steps):
        """Return a group of exits and its comparison score; lower scores are better.

        Try exits on different sides that look similarly close but take different
        numbers of steps to reach. This makes choosing an exit require reading the
        paths. After 200 tries, use the best group, or a distance-based fallback.
        """
        exit_count = 2 if self.width <= 15 else 3
        best_group = None
        best_penalty = float("inf")
        for attempt in range(200):
            group = random.sample(candidates, exit_count)
            if len({side for position, side, distance in group}) != exit_count:
                continue
            penalty = self.exit_group_penalty(group, first_steps)
            if penalty < best_penalty:
                best_group, best_penalty = group, penalty
            if penalty == 0:
                break
        if best_group is None:
            best_group = self.farthest_sides(candidates, exit_count)
            best_penalty = self.exit_group_penalty(best_group, first_steps)
        return best_group, best_penalty

    def farthest_sides(self, candidates, exit_count):
        """Return distant exit candidates on different sides as a fallback choice."""
        selected = []
        sides = set()
        for candidate in sorted(candidates, key=exit_distance, reverse=True):
            if candidate[1] not in sides:
                selected.append(candidate)
                sides.add(candidate[1])
            if len(selected) == exit_count:
                break
        return selected

    def exit_group_penalty(self, group, first_steps):
        """Score how obvious a group of exits would be to choose between.

        Prefer similar straight-line distances, moderately different walking
        distances, and more than one first move from the start. Also favor winding
        routes. These weights are estimates to tune through playtesting, rather than
        a proven measure of difficulty. A lower score is preferred.
        """
        direct = [math.dist(self.start, position) for position, side, distance in group]
        lengths = [distance for position, side, distance in group]
        visual_ratio = max(direct) / min(direct)
        route_ratio = max(lengths) / min(lengths)
        approaches = {self.get_first_move_toward_exit(position, first_steps) for position, side, distance in group}
        penalty = max(0, visual_ratio - 1.35) * 10
        penalty += max(0, 1.10 - route_ratio) * 10
        penalty += max(0, route_ratio - 1.50) * 10
        penalty += max(0, 2 - len(approaches)) * 3
        detours = [length / distance for length, distance in zip(lengths, direct)]
        penalty += max(0, 1.50 - min(detours)) * 5
        if direct.index(min(direct)) == lengths.index(min(lengths)):
            penalty += 0.5
        return penalty

    def get_first_move_toward_exit(self, position, first_steps):
        """Return the first move of one shortest route toward this boundary exit.

        Look up the adjacent interior cell, since exits are not opened yet.
        Exits whose routes both start left, for example, return the same direction.
        """
        x = min(max(position[0], 1), self.width - 2)
        y = min(max(position[1], 1), self.height - 2)
        return first_steps.get((x, y))

    def first_steps_from_start(self):
        """Use BFS to record the first move toward every reachable cell.

        Each newly seen cell inherits the first move used to reach its predecessor.
        This helps compare whether different exit routes branch near the start.
        """
        first_steps = {self.start: None}
        queue = deque([self.start])
        while queue:
            position = queue.popleft()
            x, y = position
            for dx, dy in DIRECTIONS:
                neighbor = (x + dx, y + dy)
                if self.is_open(*neighbor) and neighbor not in first_steps:
                    first_steps[neighbor] = first_steps[position]
                    if position == self.start:
                        first_steps[neighbor] = (dx, dy)
                    queue.append(neighbor)
        return first_steps

    def exit_candidates(self, distances):
        """Return possible edge openings as (position, side, distance) tuples.

        Check each boundary cell beside the interior. An interior distance of 19,
        for example, gives its possible edge exit a walking distance of 20.
        """
        candidates = []
        for x in range(1, self.width - 1):
            self.add_exit_candidate(candidates, (x, 0), (x, 1), 0, distances)
            self.add_exit_candidate(candidates, (x, self.height - 1), (x, self.height - 2), 1, distances)
        for y in range(1, self.height - 1):
            self.add_exit_candidate(candidates, (0, y), (1, y), 2, distances)
            self.add_exit_candidate(candidates, (self.width - 1, y), (self.width - 2, y), 3, distances)
        return candidates

    def add_exit_candidate(self, candidates, position, inside, side, distances):
        """Append an edge exit if its interior neighbor has a known walking distance."""
        if inside in distances:
            candidates.append((position, side, distances[inside] + 1))

    def distances_from_start(self):
        """Use BFS to return the walking distance to every reachable cell.

        Before exits are opened, these distances help evaluate possible exits.
        A path cell next to the start receives distance 1.
        """
        distances = {self.start: 0}
        queue = deque([self.start])
        while queue:
            x, y = queue.popleft()
            for dx, dy in DIRECTIONS:
                neighbor = (x + dx, y + dy)
                if self.is_open(*neighbor) and neighbor not in distances:
                    distances[neighbor] = distances[(x, y)] + 1
                    queue.append(neighbor)
        return distances

    def choose_start(self):
        """Choose an open starting cell at least two cells from each outer edge."""
        candidates = []
        for y in range(2, self.height - 2):
            for x in range(2, self.width - 2):
                if self.is_open(x, y):
                    candidates.append((x, y))
        self.start = random.choice(candidates)


# ----------------------------------------------------------------------
# PLAYER MOVEMENT
# ----------------------------------------------------------------------
# Position, route, and steps belong to Player. Game decides when moves are allowed.

class Player:
    """Track only the player's position, route, and number of moves."""

    def __init__(self, start):
        """Place the player at start with a one-cell route and zero steps.

        >>> player = Player((1, 1))
        >>> player.position
        (1, 1)
        >>> player.path
        [(1, 1)]
        >>> player.steps
        0
        """
        self.position = start
        self.path = [start]
        self.steps = 0

    def move(self, dx, dy, maze):
        """Try one horizontal or vertical step; return whether the move succeeded.

        Reject diagonal, multi-cell, and blocked moves. A valid move updates the
        position and route and adds one step, even when returning to an earlier cell.
        """
        if abs(dx) + abs(dy) != 1:
            return False
        x, y = self.position
        destination = (x + dx, y + dy)
        if not maze.is_open(*destination):
            return False
        self.position = destination
        self.path.append(destination)
        self.steps += 1
        return True


# ----------------------------------------------------------------------
# WAITING-SCREEN BFS AND DFS
# ----------------------------------------------------------------------
# A separate sample alternates BFS and DFS while the real maze is hidden.

class SampleMaze(Maze):
    """A separate, single-exit maze used only for the waiting animation."""

    def __init__(self):
        """Create a separate, one-exit maze using level 100's settings.

        The waiting screen uses its own maze so pausing does not leave the real
        layout visible while the countdown is stopped.
        """
        self.width, self.height, self.extra_openings = LEVELS[-1]
        self.start = (1, 1)
        self.exits = {(self.width - 2, self.height - 1)}
        self.cleared = False
        self.create_paths()
        self.add_connecting_paths()
        self.grid[self.height - 1][self.width - 2] = 0


class DemoSearch:
    """Animate BFS and DFS and show only the independent sample's found routes."""

    def __init__(self):
        """Create the waiting-screen sample and begin its first BFS search."""
        self.maze = SampleMaze()
        self.method = "BFS"
        self.reset()

    def reset(self):
        """Clear the previous search and put the sample start in the waiting list."""
        self.cells_to_check = deque([self.maze.start])
        self.seen_cells = {self.maze.start}
        self.previous_cells = {self.maze.start: None}
        self.path = []
        self.checked_cells = []
        self.current = self.maze.start
        self.found = False
        self.next_step = time.perf_counter()

    def tick(self):
        """Advance a few search steps when their display time arrives.

        Process up to four cells per tick so the dense sample moves visibly. Hold
        a found path for three seconds, then switch between BFS and DFS. Deadlines
        keep the window responsive while the animation runs.
        """
        now = time.perf_counter()
        if now < self.next_step:
            return
        if self.found or not self.cells_to_check:
            self.method = "DFS" if self.method == "BFS" else "BFS"
            self.reset()
            return
        for step in range(4):
            if not self.cells_to_check or self.found:
                break
            self.visit_next()
        delay = 0.045
        if self.found:
            delay = 3.0
        self.next_step = now + delay

    def visit_next(self):
        """Check the oldest waiting cell for BFS, or the newest for DFS.

        If it is the exit, build the found path. Otherwise add its open neighbors
        to the cells waiting to be checked.
        """
        if self.method == "BFS":
            self.current = self.cells_to_check.popleft()
        else:
            self.current = self.cells_to_check.pop()
        self.checked_cells.append(self.current)
        self.found = self.current in self.maze.exits
        if self.found:
            self.build_exit_path()
        else:
            self.expand()

    def build_exit_path(self):
        """Follow previous_cells from the sample exit to the start, then reverse the path."""
        self.path = []
        position = self.current
        while position is not None:
            self.path.append(position)
            position = self.previous_cells[position]
        self.path.reverse()

    def expand(self):
        """Add unseen open neighbors to the waiting list and remember how each was reached."""
        x, y = self.current
        for dx, dy in DIRECTIONS:
            neighbor = (x + dx, y + dy)
            if self.maze.is_open(*neighbor) and neighbor not in self.seen_cells:
                self.seen_cells.add(neighbor)
                self.previous_cells[neighbor] = self.current
                self.cells_to_check.append(neighbor)


# ----------------------------------------------------------------------
# GAME RULES AND PROGRESS
# ----------------------------------------------------------------------
# Game coordinates attempts, active time, scoring, retries, and level access.

class Game:
    """Keep track of attempts, points, and progress through the levels."""

    def __init__(self):
        """Start a session at level 1 with zero points and a ready attempt."""
        self.level = 0
        self.highest_unlocked_level = 0
        self.solved_counts = [0] * len(LEVELS)
        self.level_points = [0] * len(LEVELS)
        self.failures = [0] * len(LEVELS)
        self.previous_layouts = {}
        self.level_mazes = {}
        self.completed_levels = set()
        self.total_score = 0
        self.demo = DemoSearch()
        self.prepare_maze()
        self.new_attempt()

    def prepare_maze(self):
        """Load this level's unfinished maze, or generate one if none is available.

        A cleared maze is replaced when preparing the next visit. Retrying an
        unfinished maze keeps its layout, start, and exits.
        """
        saved = self.level_mazes.get(self.level)
        if saved is None or saved.cleared:
            previous = self.previous_layouts.get(self.level)
            self.level_mazes[self.level] = Maze(self.level, previous)
            self.previous_layouts[self.level] = self.level_mazes[self.level].get_wall_pattern()
        self.maze = self.level_mazes[self.level]

    def new_attempt(self, check_deadline=True):
        """Reset the current maze to the ready screen; return whether reset succeeds.

        Restarting a live or paused attempt costs points and one failure, so retry
        cannot supply free planning time. Check for timeout before charging a retry.
        A locked level cannot reset until the previous level restores access.
        """
        abandoned = False
        if check_deadline and hasattr(self, "started_at"):
            self.check_bomb()
            abandoned = self.abandon_attempt()
        if self.level > self.highest_unlocked_level:
            return False
        self.player = Player(self.maze.start)
        self.step_limit = math.floor(self.maze.shortest_distance * STEP_ALLOWANCE)
        self.bomb_seconds = bomb_duration(self.maze.shortest_distance)
        self.reset_attempt_state()
        if abandoned:
            self.message = "Restarted: -100 points and one failure."
        return True

    def abandon_attempt(self):
        """End a live or paused attempt, charge its retry penalty once, and return True."""
        if self.mode not in ("playing", "paused"):
            return False
        self.final_time = self.elapsed_time()
        self.mode = "finished"
        self.passed = False
        self.attempt_score = -RESTART_PENALTY
        self.message = "Attempt abandoned. Restarting counts as a failure."
        self.record_failure()
        self.add_attempt_score()
        return True

    def add_attempt_score(self):
        """Add this attempt's reward or penalty to the overall and current-level totals."""
        self.total_score += self.attempt_score
        self.level_points[self.level] += self.attempt_score

    def level_ready(self):
        """Return whether maze passes, net level points, and overall points allow advancement."""
        enough_mazes = self.solved_counts[self.level] >= MAZES_PER_LEVEL
        enough_points = self.level_points[self.level] >= LEVEL_POINTS_REQUIRED
        return enough_mazes and enough_points and self.total_score >= 0

    def reset_attempt_state(self):
        """Clear the attempt result and timer, leaving the player ready to press Start."""
        self.passed = False
        self.perfect = False
        self.attempt_score = 0
        self.final_time = 0
        self.started_at = None
        self.active_seconds = 0
        self.mode = "ready"
        self.message = ""
        self.level_popup = False
        self.popup_until = 0
        self.level_complete_notice = False
        self.just_completed_level = False
        self.failure_reason = None

    def toggle_play(self):
        """Start, pause, or resume the same attempt; return whether the state changed.

        Pausing saves the active time so the paused interval does not use countdown
        time or reduce the score. Drawing shows the separate sample while paused.
        An expired countdown explodes before a pause can take effect.
        """
        if self.mode == "finished" or self.level > self.highest_unlocked_level:
            return False
        if self.mode == "playing":
            if self.check_bomb():
                return False
            self.active_seconds = self.elapsed_time()
            self.started_at = None
            self.mode = "paused"
        else:
            self.started_at = time.perf_counter()
            self.mode = "playing"
        return True

    def elapsed_time(self):
        """Return active seconds played, excluding pauses and freezing at the final time."""
        if self.mode == "finished":
            return self.final_time
        if self.mode == "playing":
            return self.active_seconds + time.perf_counter() - self.started_at
        return self.active_seconds

    def time_remaining(self):
        """Return countdown seconds remaining, keeping the result from going below zero."""
        return max(0, self.bomb_seconds - self.elapsed_time())

    def check_bomb(self):
        """Explode an expired playing attempt and return True; otherwise return False."""
        if self.mode == "playing" and self.elapsed_time() >= self.bomb_seconds:
            self.explode_main_bomb()
            return True
        return False

    def explode_main_bomb(self):
        """End a timed-out attempt at its deadline and charge its penalty once."""
        if self.mode == "finished":
            return
        self.final_time = self.bomb_seconds
        self.mode = "finished"
        self.passed = False
        self.failure_reason = "main"
        self.attempt_score = -TIMEOUT_PENALTY
        self.message = "Time's up! The main bomb exploded!"
        self.record_failure()
        self.add_attempt_score()

    def move(self, dx, dy):
        """Try a player move, then check the step allowance and exits.

        The clock is checked first, so reaching an exit at exactly zero is too late.
        The first valid move beyond the step limit ends the attempt anywhere in the
        maze. Blocked moves do not count.
        """
        if self.mode != "playing" or self.check_bomb():
            return
        if not self.player.move(dx, dy, self.maze):
            return
        if self.player.steps > self.step_limit or self.player.position in self.maze.exits:
            self.finish_attempt()

    def steps_running_low(self):
        """Return True during an attempt once a tenth of the step limit (at least 3) remains.

        The limit itself stays hidden; this only warns that it is close.
        """
        if self.mode not in ("playing", "paused"):
            return False
        return self.step_limit - self.player.steps <= max(3, self.step_limit // 10)

    def finish_attempt(self):
        """Freeze an exit or over-limit result, post its score, and check progression."""
        if self.mode != "playing" or self.check_bomb():
            return
        self.final_time = self.elapsed_time()
        self.mode = "finished"
        self.passed = self.player.steps <= self.step_limit
        if self.passed:
            self.reward_success()
        else:
            self.penalize_failure()
        self.add_attempt_score()
        if self.passed:
            self.unlock_next_level()

    def reward_success(self):
        """Calculate escape points, add a shortest-route bonus when earned, and count the pass."""
        self.failures[self.level] = 0
        self.perfect = self.player.steps == self.maze.shortest_distance
        self.attempt_score = escape_points(
            self.maze.shortest_distance, self.player.steps,
            self.time_remaining(), self.bomb_seconds)
        if self.perfect:
            self.attempt_score += PERFECT_BONUS
            self.message = "Perfect route! You found a shortest way out. +250 bonus!"
        else:
            self.message = "Escaped! Efficient work."
        self.record_success()

    def record_success(self):
        """Count this maze once and mark it cleared.

        Replaying a cleared maze is practice and awards no additional points. After
        ten passes, fresh mazes can still earn missing points while the count stays ten.
        """
        if self.maze.cleared:
            self.attempt_score = 0
            self.message = "Practice complete. This maze was already counted."
            return
        self.maze.cleared = True
        self.solved_counts[self.level] = min(MAZES_PER_LEVEL, self.solved_counts[self.level] + 1)
        count = self.solved_counts[self.level]
        self.message += f" {count}/{MAZES_PER_LEVEL} mazes passed."
        if count == MAZES_PER_LEVEL:
            self.just_completed_level = self.level not in self.completed_levels

    def unlock_next_level(self):
        """Unlock the next level when both the quota and score requirements are met.

        The attempt reward must be posted before this check. A newly completed or
        reopened level shows a short celebration before automatic advancement.
        """
        if not self.level_ready():
            self.explain_score_requirement()
            return
        self.completed_levels.add(self.level)
        newly_unlocked = self.level + 1 > self.highest_unlocked_level and self.level < len(LEVELS) - 1
        if self.level < len(LEVELS) - 1:
            self.highest_unlocked_level = max(self.highest_unlocked_level, self.level + 1)
            self.failures[self.level + 1] = 0
        if self.just_completed_level or newly_unlocked:
            self.level_popup = True
            self.popup_until = time.perf_counter() + 1.2
            self.level_complete_notice = True
            self.message = ""

    def explain_score_requirement(self):
        """After ten passes, add a message explaining any remaining point shortfall."""
        if self.solved_counts[self.level] < MAZES_PER_LEVEL:
            return
        needed = max(0, LEVEL_POINTS_REQUIRED - self.level_points[self.level])
        if needed:
            self.message += f" Earn {needed:,} more net level points on fresh mazes."
        elif self.total_score < 0:
            self.message += " Earn points on fresh mazes to clear your negative total."

    def advance_after_popup(self):
        """Close an expired celebration and advance, checking time without stopping the loop."""
        if not self.level_popup or time.perf_counter() < self.popup_until:
            return False
        self.level_popup = False
        self.advance()
        return True

    def penalize_failure(self):
        """Calculate the step-limit penalty and count one failure."""
        self.attempt_score = -step_penalty(
            self.player.steps, self.step_limit, self.maze.shortest_distance)
        self.failure_reason = "steps"
        self.message = "Too many steps! The bomb exploded!"
        self.record_failure()

    def record_failure(self):
        """Add one failure and apply the lockout rule if the threshold is reached."""
        self.failures[self.level] += 1
        if self.failures[self.level] >= LOCK_AFTER_FAILURES:
            self.lock_current_level()

    def lock_current_level(self):
        """Require the previous level again after repeated failures; keep level 1 open."""
        if self.level > 0:
            self.highest_unlocked_level = self.level - 1
            self.message += f" Pass level {self.level} to unlock this level again."
        else:
            self.failures[0] = 0
            self.message += " Level 1 stays available for practice."

    def choose_level(self, level):
        """Select an allowed zero-based level index and return whether selection succeeded.

        Leaving a live or paused attempt can reduce points or lock a level. Recheck
        access after charging that failure. Clicking the active number during an
        unfinished attempt does nothing.
        """
        self.check_bomb()
        if level < 0 or level > self.highest_unlocked_level:
            return False
        if level == self.level and self.mode != "finished":
            return False
        if level > self.level and not self.level_ready():
            return False
        self.abandon_attempt()
        if level > self.highest_unlocked_level:
            return False
        if level > self.level and not self.level_ready():
            return False
        self.level = level
        self.prepare_maze()
        return self.new_attempt(False)

    def advance(self):
        """Open the next maze or eligible next level after a pass.

        If the level needs more passes or points, prepare another maze there.
        Return False when advancement is unavailable, including beyond level 100.
        """
        if self.mode != "finished" or not self.passed:
            return False
        if not self.level_ready():
            self.prepare_maze()
            return self.new_attempt()
        if self.level < len(LEVELS) - 1:
            return self.choose_level(self.level + 1)
        return False


# ----------------------------------------------------------------------
# SCREEN POSITIONS AND DRAGGING
# ----------------------------------------------------------------------
# Convert cells to pixels for drawing, and pixels back to cells for input.

def maze_geometry(maze, area=MAZE_AREA):
    """Return (left, top, cell_size) to fit and center this maze inside an area of the board."""
    area_left, area_top, area_width, area_height = area
    cell_size = min(area_width // maze.width, area_height // maze.height)
    left = area_left + (area_width - maze.width * cell_size) // 2
    top = area_top + (area_height - maze.height * cell_size) // 2
    return left, top, cell_size


def cell_center(position, geometry):
    """Return the screen pixel center of a cell using (left, top, cell_size).

    >>> cell_center((1, 1), (100, 50, 20))
    (130, 80)
    >>> cell_center((0, 0), (0, 0, 5))
    (2, 2)
    """
    left, top, size = geometry
    x, y = position
    return (left + x * size + size // 2, top + y * size + size // 2)


def screen_position_to_cell(position, geometry):
    """Return the maze cell under a screen pixel.

    Subtract the board offset and divide by cell size. Coordinates outside the
    board remain outside the grid so movement checks can reject them.

    >>> screen_position_to_cell((130, 80), (100, 50, 20))
    (1, 1)
    >>> screen_position_to_cell((99, 50), (100, 50, 20))
    (-1, 0)
    >>> screen_position_to_cell(cell_center((3, 2), (100, 50, 20)), (100, 50, 20))
    (3, 2)
    """
    left, top, size = geometry
    return (int((position[0] - left) // size), int((position[1] - top) // size))


def step_toward(start, target):
    """Return the one-cell move from start toward target along the longer axis.

    Tapping anywhere on the board moves one cell, so small cells on a phone
    do not have to be hit exactly.

    >>> step_toward((2, 2), (5, 3))
    (1, 0)
    >>> step_toward((2, 2), (2, 0))
    (0, -1)
    >>> step_toward((2, 2), (2, 2))
    (0, 0)
    """
    dx = target[0] - start[0]
    dy = target[1] - start[1]
    if dx == dy == 0:
        return (0, 0)
    if abs(dx) >= abs(dy):
        return (1 if dx > 0 else -1, 0)
    return (0, 1 if dy > 0 else -1)


def drag_segment(game, before, after):
    """Request moves along the mouse's path between two screen positions.

    Mouse events may skip over cells during a fast drag. Check intermediate
    positions so movement stays one cell at a time and Game checks each step.
    """
    geometry = maze_geometry(game.maze)
    dx = after[0] - before[0]
    dy = after[1] - before[1]
    samples = max(1, math.ceil(max(abs(dx), abs(dy)) / (geometry[2] / 5)))
    for index in range(1, samples + 1):
        pixel = (before[0] + dx * index / samples, before[1] + dy * index / samples)
        target_x, target_y = screen_position_to_cell(pixel, geometry)
        x, y = game.player.position
        if abs(target_x - x) + abs(target_y - y) == 1:
            game.move(target_x - x, target_y - y)


# ----------------------------------------------------------------------
# DRAWING AND CONTROLS
# ----------------------------------------------------------------------
# Drawing reads the current game state and builds the visible controls.
# The look is a cartoon comic: thick black outlines, hard black shadows,
# and bold colors on a sky-blue background.

# ---- Fonts and text ----

def load_font(pygame, file_name, size, bold=False):
    """Load a font from the fonts folder, or pygame's default font if the file is missing."""
    try:
        font = pygame.font.Font(os.path.join(FONT_FOLDER, file_name), size)
    except (FileNotFoundError, OSError):
        font = pygame.font.Font(None, size + 6)
    font.bold = bold
    return font


def make_fonts(pygame):
    """Return the fonts by name: comic lettering for headings, Nunito for sentences."""
    return {"title": load_font(pygame, COMIC_FONT, 54),
            "stamp": load_font(pygame, COMIC_FONT, 110),
            "timer": load_font(pygame, COMIC_FONT, 50),
            "big": load_font(pygame, COMIC_FONT, 36),
            "level": load_font(pygame, COMIC_FONT, 30),
            "button": load_font(pygame, COMIC_FONT, 24),
            "label": load_font(pygame, COMIC_FONT, 21),
            "text": load_font(pygame, TEXT_FONT, 17, bold=True),
            "small": load_font(pygame, TEXT_FONT, 15, bold=True)}


def draw_text(screen, font, text, position, color=INK):
    """Draw text with its top-left corner at the given pixel position."""
    screen.blit(font.render(text, True, color), position)


def draw_centered_text(screen, font, text, center, color=INK):
    """Draw text centered on the given pixel position."""
    image = font.render(text, True, color)
    screen.blit(image, image.get_rect(center=center))


def draw_wrapped_text(screen, font, text, x, y, width, color=INK):
    """Draw text one word at a time, starting a new line when the width is exceeded.

    Return the y position just below the last line, so more text can follow it.
    """
    line = ""
    for word in text.split():
        candidate = (line + " " + word).strip()
        if font.size(candidate)[0] > width and line:
            draw_text(screen, font, line, (x, y), color)
            y += font.get_linesize() + 3
            line = word
        else:
            line = candidate
    draw_text(screen, font, line, (x, y), color)
    return y + font.get_linesize()


def comic_text(pygame, font, text, color, outline=3, shadow=4):
    """Return an image of text with a black outline and a hard black shadow, like a comic title."""
    ink = font.render(text, True, INK)
    fill = font.render(text, True, color)
    width = fill.get_width() + outline * 2 + shadow
    height = fill.get_height() + outline * 2 + shadow
    image = pygame.Surface((width, height), pygame.SRCALPHA)
    # Shadow first, then black copies all around for the outline, then the colored letters on top.
    image.blit(ink, (outline + shadow, outline + shadow))
    for dx in range(-outline, outline + 1):
        for dy in range(-outline, outline + 1):
            if dx * dx + dy * dy <= outline * outline:
                image.blit(ink, (outline + dx, outline + dy))
    image.blit(fill, (outline, outline))
    return image


def format_countdown(seconds):
    """Return seconds as a stopwatch reading, rounded up to the next tenth of a second.

    >>> format_countdown(31.42)
    '00:31.5'
    >>> format_countdown(75)
    '01:15.0'
    >>> format_countdown(0)
    '00:00.0'
    """
    tenths = math.ceil(round(seconds * 10, 6))
    minutes, tenths = divmod(tenths, 600)
    return f"{minutes:02d}:{tenths // 10:02d}.{tenths % 10}"


# ---- Panels and background ----

background_image = None  # Made once by draw_background, then reused every frame.


def draw_background(pygame, screen):
    """Fill the screen with sky blue and small light dots, like comic-book printing.

    Drawing thousands of dots every frame would be slow, so the finished
    background is saved the first time and copied after that.
    """
    global background_image
    if background_image is None:
        background_image = pygame.Surface((WINDOW_WIDTH, WINDOW_HEIGHT))
        background_image.fill(SKY)
        for y in range(8, WINDOW_HEIGHT, 16):
            for x in range(8, WINDOW_WIDTH, 16):
                pygame.draw.circle(background_image, SKY_DOTS, (x, y), 2)
    screen.blit(background_image, (0, 0))


def draw_card(pygame, screen, rect, fill=WHITE, shadow=4):
    """Draw a comic panel: a hard black shadow, then a filled box with a thick black outline."""
    pygame.draw.rect(screen, INK, rect.move(shadow, shadow), border_radius=14)
    pygame.draw.rect(screen, fill, rect, border_radius=14)
    pygame.draw.rect(screen, INK, rect, width=3, border_radius=14)


def draw_shade(pygame, screen):
    """Darken the whole screen so a panel on top of it stands out."""
    shade = pygame.Surface(screen.get_size(), pygame.SRCALPHA)
    shade.fill((12, 30, 48, 165))
    screen.blit(shade, (0, 0))


# ---- Pictures: bomb, spark, flag, player, and icons ----

def curve_point(start, bend, end, t):
    """Return the point a fraction t (0 to 1) along a smooth curve that bends toward bend.

    >>> curve_point((0, 0), (5, 10), (10, 0), 0.5)
    (5.0, 5.0)
    """
    a = (1 - t) ** 2
    b = 2 * (1 - t) * t
    c = t ** 2
    return (a * start[0] + b * bend[0] + c * end[0],
            a * start[1] + b * bend[1] + c * end[1])


def draw_bomb(pygame, screen, center, radius, fuse, spark_size=0, color=INK):
    """Draw a cartoon bomb with a fuse that is `fuse` long, from 1 (full) to 0 (burned away)."""
    x, y = center
    # The fuse follows a curve up from the cap. A shorter fuse stops part of the way along.
    start = (x + radius * 0.55, y - radius * 0.95)
    bend = (x + radius * 0.75, y - radius * 1.6)
    end = (x + radius * 1.35, y - radius * 1.75)
    fuse_points = [curve_point(start, bend, end, fuse * step / 10) for step in range(11)]
    if fuse > 0:
        pygame.draw.lines(screen, FUSE_BROWN, False, fuse_points, max(2, radius // 9))
    cap = pygame.Rect(0, 0, radius * 0.6, radius * 0.45)
    cap.center = (x + radius * 0.5, y - radius * 0.82)
    pygame.draw.rect(screen, (110, 110, 110), cap, border_radius=3)
    pygame.draw.rect(screen, INK, cap, 2, border_radius=3)
    pygame.draw.circle(screen, color, center, radius)
    pygame.draw.circle(screen, INK, center, radius, 2)
    shine = pygame.Rect(0, 0, radius * 0.5, radius * 0.32)
    shine.center = (x - radius * 0.35, y - radius * 0.38)
    pygame.draw.ellipse(screen, (120, 120, 120) if color == INK else WHITE, shine)
    if spark_size and fuse > 0:
        draw_spark(pygame, screen, fuse_points[-1], spark_size)


def draw_spark(pygame, screen, center, size):
    """Draw a spark: short orange rays around a yellow dot with a white middle."""
    x, y = center
    for index in range(8):
        angle = index * math.pi / 4
        tip = (x + math.cos(angle) * size, y + math.sin(angle) * size)
        pygame.draw.line(screen, SPARK_ORANGE, center, tip, 3)
    pygame.draw.circle(screen, YELLOW, center, size / 2)
    pygame.draw.circle(screen, WHITE, center, max(2, size / 5))


def draw_flag(pygame, screen, center, size):
    """Draw a green flag on a black pole to mark an exit."""
    x, y = center
    pole_x = x - size * 0.3
    pole_top = y - size * 0.6
    pygame.draw.line(screen, INK, (pole_x, pole_top), (pole_x, y + size * 0.5), max(2, size // 8))
    flag = [(pole_x, pole_top), (x + size * 0.55, pole_top + size * 0.25), (pole_x, pole_top + size * 0.5)]
    pygame.draw.polygon(screen, GREEN, flag)
    pygame.draw.polygon(screen, INK, flag, max(1, size // 10))


def draw_player(pygame, screen, center, size):
    """Draw the player: a yellow face with two black eyes."""
    x, y = center
    radius = max(4, size * 0.45)
    pygame.draw.circle(screen, YELLOW, center, radius)
    pygame.draw.circle(screen, INK, center, radius, max(1, size // 10))
    for side in (-1, 1):
        pygame.draw.circle(screen, INK, (x + side * radius * 0.35, y - radius * 0.15), max(1, radius * 0.18))


ARROW_DIRECTIONS = {"left": (-1, 0), "right": (1, 0), "up": (0, -1), "down": (0, 1)}


def draw_arrow(pygame, screen, center, direction, color, length=11):
    """Draw an arrow pointing in a direction, such as (1, 0) for right."""
    x, y = center
    dx, dy = direction
    tip = (x + dx * length, y + dy * length)
    tail = (x - dx * length, y - dy * length)
    pygame.draw.line(screen, color, tail, tip, 4)
    # The two short lines of the arrowhead go back from the tip, one on each side.
    side_x, side_y = -dy, dx
    for sign in (1, -1):
        wing = (tip[0] - dx * 7 + side_x * 7 * sign, tip[1] - dy * 7 + side_y * 7 * sign)
        pygame.draw.line(screen, color, tip, wing, 4)


def draw_speaker(pygame, screen, center, color, sound_on):
    """Draw a speaker with sound waves when sound is on, or with an X when it is muted."""
    x, y = center
    body = [(x - 11, y - 4), (x - 6, y - 4), (x + 1, y - 10), (x + 1, y + 10), (x - 6, y + 4), (x - 11, y + 4)]
    pygame.draw.polygon(screen, color, body)
    if sound_on:
        # Each sound wave is a short curve made of points around a circle.
        for radius in (7, 12):
            wave = []
            for step in range(9):
                angle = -0.8 + step * 0.2
                wave.append((x + 1 + math.cos(angle) * radius, y + math.sin(angle) * radius))
            pygame.draw.lines(screen, color, False, wave, 3)
    else:
        pygame.draw.line(screen, color, (x + 5, y - 5), (x + 13, y + 5), 3)
        pygame.draw.line(screen, color, (x + 5, y + 5), (x + 13, y - 5), 3)


# ---- Buttons ----

def level_choice_allowed(game, index):
    """Return whether the player may switch to the level with this zero-based index."""
    if index < 0 or index >= len(LEVELS) or index > game.highest_unlocked_level:
        return False
    return index <= game.level or game.level_ready()


def make_buttons(pygame, game, sound_on=True):
    """Return every button for this frame: level arrows, attempt controls, help, sound, and moves."""
    buttons = make_level_buttons(pygame, game)
    buttons.extend(make_attempt_buttons(pygame, game))
    buttons.append(Button(label="?", rect=pygame.Rect(826, 22, 42, 42), action="help"))
    buttons.append(Button(label="Sound: on" if sound_on else "Sound: off",
                          rect=pygame.Rect(888, 22, 42, 42), action="sound",
                          icon="sound_on" if sound_on else "sound_off"))
    for index, name in enumerate(["left", "up", "down", "right"]):
        rect = pygame.Rect(669 + index * 66, BOTTOM_ROW, 60, BOTTOM_HEIGHT)
        buttons.append(Button(label=name.title(), rect=rect, action="move", icon=name,
                              value=ARROW_DIRECTIONS[name], enabled=game.mode != "finished"))
    return buttons


def make_level_buttons(pygame, game):
    """Build the two small arrows beside the level name that step one level back or forward."""
    back = game.level - 1
    forward = game.level + 1
    return [Button(label="Back one level", rect=pygame.Rect(456, 24, 36, 36), action="level",
                   value=back, icon="left", enabled=level_choice_allowed(game, back)),
            Button(label="Forward one level", rect=pygame.Rect(606, 24, 36, 36), action="level",
                   value=forward, icon="right", enabled=level_choice_allowed(game, forward))]


def make_attempt_buttons(pygame, game):
    """Build retry, play, advance, and previous-level recovery controls from the game state."""
    retry_rect = pygame.Rect(162, BOTTOM_ROW, 155, BOTTOM_HEIGHT)
    next_rect = pygame.Rect(329, BOTTOM_ROW, 135, BOTTOM_HEIGHT)
    can_retry = game.level <= game.highest_unlocked_level
    level_done = game.level_ready()
    can_advance = game.mode == "finished" and game.passed and (not level_done or game.level < len(LEVELS) - 1)
    next_label = "Next level" if level_done else "Next maze"
    if not level_done and game.solved_counts[game.level] == MAZES_PER_LEVEL:
        next_label = "Earn points"
    buttons = [Button(label="New attempt", rect=retry_rect, action="retry", enabled=can_retry),
               make_play_button(pygame, game, can_retry),
               Button(label=next_label, rect=next_rect, action="next", enabled=can_advance)]
    if game.level > game.highest_unlocked_level:
        rect = pygame.Rect(476, BOTTOM_ROW, 165, BOTTOM_HEIGHT)
        buttons.append(Button(label="Previous level", rect=rect,
                              action="level", value=game.level - 1))
    return buttons


def make_play_button(pygame, game, can_retry):
    """Return the Start, Pause, or Resume button for the current attempt mode."""
    labels = {"ready": "Start", "playing": "Pause", "paused": "Resume", "finished": "Start"}
    return Button(label=labels[game.mode], rect=pygame.Rect(30, BOTTOM_ROW, 120, BOTTOM_HEIGHT),
                  action="play", enabled=can_retry and game.mode != "finished")


def draw_button(pygame, screen, fonts, button):
    """Draw a comic button: white (yellow for Start/Pause) with a black outline and shadow.

    Disabled buttons are flat and pale blue, so they clearly cannot be clicked.
    """
    rect = button.rect
    if button.enabled:
        fill = YELLOW if button.action == "play" else WHITE
        ink = INK
        pygame.draw.rect(screen, INK, rect.move(4, 4), border_radius=12)
    else:
        fill = DISABLED_FILL
        ink = DISABLED_TEXT
    pygame.draw.rect(screen, fill, rect, border_radius=12)
    pygame.draw.rect(screen, ink, rect, 3, border_radius=12)
    if button.icon in ARROW_DIRECTIONS:
        length = 11 if rect.width > 40 else 8
        draw_arrow(pygame, screen, rect.center, ARROW_DIRECTIONS[button.icon], ink, length)
    elif button.icon in ("sound_on", "sound_off"):
        draw_speaker(pygame, screen, rect.center, ink, button.icon == "sound_on")
    else:
        draw_centered_text(screen, fonts["button"], button.label.upper(), rect.center, ink)


# ---- The whole screen ----

def draw_game(pygame, screen, fonts, game, sound_on=True, show_help=False, effect_age=None):
    """Draw the whole screen and return the buttons that can be clicked right now.

    effect_age is the number of seconds since the attempt finished. The shake,
    the stamp, and the confetti use it to move.
    """
    draw_background(pygame, screen)
    draw_heading(pygame, screen, fonts, game)
    draw_statistics(pygame, screen, fonts, game)
    draw_board(pygame, screen, fonts, game, effect_age)
    draw_messages(screen, fonts, game)
    draw_confetti(pygame, screen, game, effect_age)
    draw_result_stamp(pygame, screen, fonts, game, effect_age)
    buttons = make_buttons(pygame, game, sound_on)
    for button in buttons:
        draw_button(pygame, screen, fonts, button)
    if game.level_popup:
        return draw_level_popup(pygame, screen, fonts, game)
    if show_help:
        return draw_help(pygame, screen, fonts)
    return buttons


# ---- Top row: title, name sticker, level, and maze dots ----

def draw_heading(pygame, screen, fonts, game):
    """Draw the title, the "by BIOR" sticker, the level name, and the maze progress dots."""
    title = comic_text(pygame, fonts["title"], "BEAT THE BLAST", YELLOW)
    screen.blit(title, (26, 12))
    draw_name_sticker(pygame, screen, fonts, (26 + title.get_width() + 6, 20))
    level_name = comic_text(pygame, fonts["level"], f"LEVEL {game.level + 1}", WHITE, outline=2, shadow=3)
    screen.blit(level_name, level_name.get_rect(center=(549, 43)))
    draw_maze_dots(pygame, screen, fonts, game)


def draw_name_sticker(pygame, screen, fonts, position):
    """Draw a small tilted red sticker that says "by BIOR"."""
    text = fonts["label"].render("by BIOR", True, WHITE)
    sticker = pygame.Surface((text.get_width() + 20, text.get_height() + 8), pygame.SRCALPHA)
    pygame.draw.rect(sticker, RED, sticker.get_rect(), border_radius=8)
    pygame.draw.rect(sticker, INK, sticker.get_rect(), 3, border_radius=8)
    sticker.blit(text, (10, 4))
    screen.blit(pygame.transform.rotate(sticker, 8), position)


def draw_maze_dots(pygame, screen, fonts, game):
    """Draw ten dots for this level's ten mazes: orange for passed mazes, white for the rest."""
    passed = game.solved_counts[game.level]
    for index in range(MAZES_PER_LEVEL):
        center = (668 + index * 15, 33)
        pygame.draw.circle(screen, SPARK_ORANGE if index < passed else WHITE, center, 6)
        pygame.draw.circle(screen, INK, center, 6, 2)
    maze_number = min(MAZES_PER_LEVEL, passed + (not game.maze.cleared))
    draw_text(screen, fonts["small"], f"Maze {maze_number} of {MAZES_PER_LEVEL}", (662, 44))


# ---- Left column: bomb timer, steps, lives, and points ----

def draw_statistics(pygame, screen, fonts, game):
    """Draw the four cards in the left column."""
    draw_bomb_card(pygame, screen, fonts, game)
    draw_steps_card(pygame, screen, fonts, game)
    draw_lives_card(pygame, screen, fonts, game)
    draw_points_card(pygame, screen, fonts, game)


def fuse_left(game):
    """Return how much of the fuse is left, from 1.0 (full) down to 0.0 (burned away)."""
    if game.failure_reason is not None or game.bomb_seconds <= 0:
        return 0
    return game.time_remaining() / game.bomb_seconds


def draw_bomb_card(pygame, screen, fonts, game):
    """Draw the bomb, whose fuse burns down with the countdown, and the countdown itself.

    In the last ten seconds the spark grows and the countdown blinks.
    """
    card = pygame.Rect(CARD_LEFT, 84, CARD_WIDTH, 192)
    draw_card(pygame, screen, card)
    remaining = game.time_remaining()
    danger = game.mode == "playing" and remaining <= 10
    spark = 0
    if game.mode != "finished":
        flicker = math.sin(time.perf_counter() * 25) * 2
        spark = (13 if danger else 9) + flicker
    draw_bomb(pygame, screen, (card.centerx - 8, card.y + 82), 38, fuse_left(game), spark)
    color = RED
    if danger and int(time.perf_counter() * 4) % 2:
        color = INK
    draw_centered_text(screen, fonts["timer"], format_countdown(remaining), (card.centerx, card.bottom - 34), color)


def draw_steps_card(pygame, screen, fonts, game):
    """Draw the steps taken so far, with a warning when the hidden step limit is close."""
    low = game.steps_running_low()
    card = pygame.Rect(CARD_LEFT, 288, CARD_WIDTH, 96)
    draw_card(pygame, screen, card, CHECKED_YELLOW if low else WHITE)
    draw_text(screen, fonts["label"], "STEPS TAKEN", (card.x + 16, card.y + 10))
    draw_text(screen, fonts["big"], str(game.player.steps), (card.x + 16, card.y + 34))
    if low:
        draw_text(screen, fonts["small"], "Few steps left!", (card.x + 88, card.y + 50), RED)


def draw_lives_card(pygame, screen, fonts, game):
    """Draw three small bombs; each failure in a row turns one grey."""
    card = pygame.Rect(CARD_LEFT, 396, CARD_WIDTH, 96)
    draw_card(pygame, screen, card)
    draw_text(screen, fonts["label"], "LIVES", (card.x + 16, card.y + 10))
    lost = min(LOCK_AFTER_FAILURES, game.failures[game.level])
    for index in range(LOCK_AFTER_FAILURES):
        is_lost = index >= LOCK_AFTER_FAILURES - lost
        color = LOST_GREY if is_lost else INK
        fuse = 0 if is_lost else 0.5
        draw_bomb(pygame, screen, (card.x + 32 + index * 46, card.y + 62), 14, fuse, 0, color)


def draw_points_card(pygame, screen, fonts, game):
    """Draw the total points and this level's progress toward the points it needs."""
    card = pygame.Rect(CARD_LEFT, 504, CARD_WIDTH, 108)
    draw_card(pygame, screen, card)
    draw_text(screen, fonts["label"], "POINTS", (card.x + 16, card.y + 10))
    draw_text(screen, fonts["big"], f"{game.total_score:+,}", (card.x + 16, card.y + 34))
    level_points = f"This level: {game.level_points[game.level]:,} / {LEVEL_POINTS_REQUIRED:,}"
    draw_text(screen, fonts["small"], level_points, (card.x + 16, card.y + 78), MUTED)


# ---- The board: maze, player, exits, and effects ----

def draw_board(pygame, screen, fonts, game, effect_age=None):
    """Draw the paper board; show the search demo while ready or paused, and the real maze otherwise."""
    draw_card(pygame, screen, pygame.Rect(BOARD_RECT), PAPER, shadow=6)
    if game.mode in ("ready", "paused"):
        draw_sample(pygame, screen, fonts, game)
        return
    left, top, size = maze_geometry(game.maze)
    shake_x, shake_y = shake_offset(game, effect_age)
    geometry = (left + shake_x, top + shake_y, size)
    draw_maze(pygame, screen, game.maze, geometry)
    draw_player_path(pygame, screen, game, geometry)
    for position in game.maze.exits:
        draw_flag(pygame, screen, cell_center(position, geometry), size)
    draw_player(pygame, screen, cell_center(game.player.position, geometry), size)
    draw_blast_effect(pygame, screen, game, geometry, effect_age)


def shake_offset(game, effect_age):
    """Return how far to shift the maze while it shakes, for a moment after the bomb goes off."""
    if game.failure_reason is None or effect_age is None or effect_age > 0.6:
        return (0, 0)
    strength = 9 * (1 - effect_age / 0.6)
    return (round(math.sin(effect_age * 70) * strength), round(math.cos(effect_age * 55) * strength))


def draw_maze(pygame, screen, maze, geometry):
    """Draw the maze on paper: orange walls with a thin black outline."""
    left, top, size = geometry
    pygame.draw.rect(screen, PAPER, pygame.Rect(left, top, maze.width * size, maze.height * size))
    walls = []
    for y, row in enumerate(maze.grid):
        for x, wall in enumerate(row):
            if wall:
                walls.append(pygame.Rect(left + x * size, top + y * size, size, size))
    # Black squares a little bigger than each wall go down first, so an outline shows around the orange.
    edge = max(1, size // 8)
    for wall in walls:
        pygame.draw.rect(screen, INK, wall.inflate(edge * 2, edge * 2))
    for wall in walls:
        pygame.draw.rect(screen, WALL_ORANGE, wall)


def draw_player_path(pygame, screen, game, geometry):
    """Draw the route the player actually traveled: red, or green after a shortest-route finish.

    The game never draws a suggested solution, since finding the route is the challenge.
    """
    if len(game.player.path) < 2:
        return
    points = [cell_center(position, geometry) for position in game.player.path]
    color = GREEN if game.perfect else RED
    pygame.draw.lines(screen, color, False, points, max(2, geometry[2] // 6))


def draw_blast_effect(pygame, screen, game, geometry, effect_age=None):
    """After an explosion, draw a comic starburst where the player was. It grows quickly at first."""
    if game.failure_reason is None:
        return
    grow = 1 if effect_age is None else min(1, 0.3 + effect_age / 0.25)
    radius = max(30, geometry[2] * 3) * grow
    x, y = cell_center(game.player.position, geometry)
    points = []
    for index in range(24):
        angle = index * math.pi / 12
        reach = radius if index % 2 == 0 else radius * 0.55
        points.append((x + math.cos(angle) * reach, y + math.sin(angle) * reach))
    screen.set_clip(pygame.Rect(BOARD_RECT))
    pygame.draw.polygon(screen, YELLOW, points)
    pygame.draw.polygon(screen, INK, points, 3)
    pygame.draw.circle(screen, RED, (x, y), radius * 0.35)
    pygame.draw.circle(screen, INK, (x, y), radius * 0.35, 3)
    screen.set_clip(None)


CONFETTI_COLORS = [YELLOW, RED, GREEN, SKY, SPARK_ORANGE]


def draw_confetti(pygame, screen, game, effect_age):
    """After an escape, let confetti fall over the board for three seconds."""
    if game.mode != "finished" or not game.passed or effect_age is None or effect_age > 3:
        return
    board = pygame.Rect(BOARD_RECT)
    # The same seed gives the same pieces every frame, so each piece falls smoothly.
    chance = random.Random(7)
    screen.set_clip(board)
    for index in range(70):
        x = board.x + chance.random() * board.width
        start_y = board.y - chance.random() * 300
        speed = 180 + chance.random() * 220
        flutter = abs(math.sin(effect_age * 8 + index))  # Pieces flip over as they fall.
        piece = pygame.Rect(0, 0, 10, max(2, 14 * flutter))
        piece.center = (x + math.sin(effect_age * 3 + index) * 12, start_y + speed * effect_age)
        pygame.draw.rect(screen, CONFETTI_COLORS[index % len(CONFETTI_COLORS)], piece)
    screen.set_clip(None)


def result_words(game):
    """Return the big stamp word and the one-line summary for a finished attempt."""
    if game.passed:
        word = "PERFECT!" if game.perfect else "ESCAPED!"
        return word, f"{game.attempt_score:+,} points · {game.time_remaining():.1f}s left"
    reasons = {"main": "Out of time", "steps": "Too many steps"}
    reason = reasons.get(game.failure_reason, "Attempt abandoned")
    return "BOOM!", f"{reason} · {game.attempt_score:+,} points"


def draw_result_stamp(pygame, screen, fonts, game, effect_age):
    """After an attempt, stamp BOOM!, ESCAPED!, or PERFECT! across the maze, with a summary under it.

    The stamp starts big and quickly shrinks into place, like it was slapped on.
    """
    if game.mode != "finished" or game.level_popup:
        return
    word, summary = result_words(game)
    scale = 1.0 if effect_age is None else max(1.0, 1.6 - effect_age * 3)
    stamp = comic_text(pygame, fonts["stamp"], word, YELLOW, outline=4, shadow=7)
    stamp = pygame.transform.rotozoom(stamp, 8, scale)
    center_x = MAZE_AREA[0] + MAZE_AREA[2] // 2
    screen.blit(stamp, stamp.get_rect(center=(center_x, 300)))
    text = fonts["text"].render(summary, True, INK)
    label = pygame.Surface((text.get_width() + 28, text.get_height() + 12), pygame.SRCALPHA)
    pygame.draw.rect(label, WHITE, label.get_rect(), border_radius=10)
    pygame.draw.rect(label, INK, label.get_rect(), 3, border_radius=10)
    label.blit(text, (14, 6))
    label = pygame.transform.rotate(label, 8)
    screen.blit(label, label.get_rect(center=(center_x + 6, 382)))


def draw_sample(pygame, screen, fonts, game):
    """While waiting or paused, show the BFS or DFS search working through a sample maze."""
    demo = game.demo
    geometry = maze_geometry(demo.maze, SAMPLE_AREA)
    left, top, size = geometry
    draw_maze(pygame, screen, demo.maze, geometry)
    for x, y in demo.checked_cells:
        pygame.draw.rect(screen, CHECKED_YELLOW, pygame.Rect(left + x * size, top + y * size, size, size))
    draw_demo_path(pygame, screen, demo, geometry)
    for position in demo.maze.exits:
        draw_flag(pygame, screen, cell_center(position, geometry), size)
    draw_player(pygame, screen, cell_center(demo.current, geometry), size)
    # A label above the sample says which search is running.
    chip = pygame.Rect(0, 0, 180, 32)
    chip.center = (MAZE_AREA[0] + MAZE_AREA[2] // 2, 116)
    pygame.draw.rect(screen, YELLOW, chip, border_radius=10)
    pygame.draw.rect(screen, INK, chip, 3, border_radius=10)
    draw_centered_text(screen, fonts["button"], f"{demo.method} SEARCH", chip.center)


def draw_demo_path(pygame, screen, demo, geometry):
    """Draw the sample search's found path in green once it reaches the exit."""
    if not demo.found or len(demo.path) < 2:
        return
    points = [cell_center(position, geometry) for position in demo.path]
    pygame.draw.lines(screen, GREEN, False, points, max(2, geometry[2] // 3))


def current_tip(game):
    """Return one tip, moving to the next each time a maze is passed."""
    return TIPS[sum(game.solved_counts) % len(TIPS)]


def draw_messages(screen, fonts, game):
    """Show the latest message under the maze, or a tip when there is nothing to report."""
    if game.level_complete_notice:
        return
    if game.message:
        text = game.message
        color = RED if game.failure_reason else (DARK_GREEN if game.perfect else INK)
    elif game.mode == "paused":
        text, color = "Paused. Your maze stays hidden until you press RESUME.", INK
    else:
        text, color = "Tip: " + current_tip(game), MUTED
    left, top, width, height = MAZE_AREA
    draw_wrapped_text(screen, fonts["small"], text, left, top + height + 10, width, color)


# ---- Pop-up panels ----

def draw_level_popup(pygame, screen, fonts, game):
    """Celebrate a passed level over a darkened screen; return no buttons while it shows."""
    draw_shade(pygame, screen)
    draw_card(pygame, screen, pygame.Rect(240, 260, 480, 200), WHITE, shadow=6)
    title = comic_text(pygame, fonts["title"], f"LEVEL {game.level + 1} PASSED!", YELLOW)
    screen.blit(title, title.get_rect(center=(480, 332)))
    subtitle = f"Level {game.level + 2} unlocked!"
    if game.level == len(LEVELS) - 1:
        subtitle = "All 100 levels complete!"
    draw_centered_text(screen, fonts["text"], subtitle, (480, 402), DARK_GREEN)
    return []


def draw_help(pygame, screen, fonts):
    """Draw the How to play panel and return its one button, which closes the panel."""
    draw_shade(pygame, screen)
    draw_card(pygame, screen, pygame.Rect(170, 115, 620, 490), WHITE, shadow=6)
    title = comic_text(pygame, fonts["title"], "HOW TO PLAY", YELLOW)
    screen.blit(title, title.get_rect(center=(480, 167)))
    top = 223
    for line in HELP_LINES:
        pygame.draw.circle(screen, SPARK_ORANGE, (208, top + 11), 6)
        pygame.draw.circle(screen, INK, (208, top + 11), 6, 2)
        top = draw_wrapped_text(screen, fonts["text"], line, 226, top, 530) + 18
    close = Button(label="Got it!", rect=pygame.Rect(405, 531, 150, 52), action="help")
    draw_button(pygame, screen, fonts, close)
    return [close]


# ----------------------------------------------------------------------
# SOUND EFFECTS
# ----------------------------------------------------------------------
# Effects are built from raw samples, so the game needs no audio files.

class Sounds:
    """Build and play short effects, staying silent when audio is unavailable."""

    def __init__(self, pygame):
        """Create the clock ticks, step warning, blast, and escape sounds once."""
        self.pygame = pygame
        self.enabled = True
        self.effects = {}
        try:
            if not pygame.mixer.get_init():
                pygame.mixer.init()
            self.rate, size, self.channels = pygame.mixer.get_init()
        except (pygame.error, TypeError):
            return
        if size != -16:
            return
        try:
            self.effects = {
                "tick": self.make(self.tone(880, 0.04, 0.2)),
                "fast_tick": self.make(self.tone(1320, 0.05, 0.3)),
                "warn": self.make(self.tone(520, 0.08, 0.3) + self.tone(0, 0.05, 0)
                                  + self.tone(520, 0.08, 0.3)),
                "blast": self.make(self.blast()),
                "escape": self.make(self.notes([523, 659, 784])),
                "perfect": self.make(self.notes([523, 659, 784, 1047])),
                "unlock": self.make(self.notes([392, 523, 659, 784, 1047])),
            }
        except pygame.error:
            self.effects = {}

    def tone(self, frequency, seconds, volume):
        """Return samples for a sine tone that fades out, from -1.0 to 1.0."""
        count = int(self.rate * seconds)
        step = 2 * math.pi * frequency / self.rate
        return [volume * math.sin(step * index) * (1 - index / count) ** 2
                for index in range(count)]

    def notes(self, frequencies):
        """Return samples for a quick rising run of notes."""
        samples = []
        for frequency in frequencies:
            samples += self.tone(frequency, 0.11, 0.28)
        return samples

    def blast(self):
        """Return samples for a rumbling explosion: smoothed noise over a low boom."""
        noise = random.Random(7)
        count = int(self.rate * 0.9)
        samples = []
        rumble = 0.0
        for index in range(count):
            rumble += (noise.uniform(-1, 1) - rumble) * 0.2
            fade = (1 - index / count) ** 3
            boom = math.sin(2 * math.pi * 55 * index / self.rate)
            samples.append(fade * (1.6 * rumble + 0.35 * boom))
        return samples

    def make(self, samples):
        """Pack samples as 16-bit audio for every mixer channel and return a Sound."""
        data = array("h")
        for sample in samples:
            value = int(max(-1.0, min(1.0, sample)) * 32767)
            data.extend([value] * self.channels)
        return self.pygame.mixer.Sound(buffer=data.tobytes())

    def play(self, name):
        """Play an effect by name when sound is on and audio is available."""
        if self.enabled and name in self.effects:
            self.effects[name].play()

    def toggle(self):
        """Turn sound on or off, stopping anything still playing when muted."""
        self.enabled = not self.enabled
        if not self.enabled and self.effects:
            self.pygame.mixer.stop()


# ----------------------------------------------------------------------
# WINDOW AND INPUT HANDLING
# ----------------------------------------------------------------------
# App runs the pygame window and sends input to Game.

class App:
    """Connect input and drawing to the game rules."""

    def __init__(self):
        """Open the pygame window and create the game, fonts, clock, and input state."""
        import pygame
        self.pygame = pygame
        pygame.init()
        flags = 0 if sys.platform == "emscripten" else pygame.SCALED
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT), flags)
        pygame.display.set_caption("Beat the Blast")
        self.fonts = make_fonts(pygame)
        self.clock = pygame.time.Clock()
        pygame.key.set_repeat(160, 90)
        self.game = Game()
        self.buttons = []
        self.dragging = False
        self.previous_mouse = None
        self.running = True
        self.key_directions = self.make_key_directions()
        self.sounds = Sounds(pygame)
        self.last_mode = self.game.mode
        self.last_popup = False
        self.last_beat = None
        self.warned = False
        self.show_help = True      # How to play opens when the game starts.
        self.finished_at = None    # When the current attempt finished, for animations.

    def make_key_directions(self):
        """Return the cell movement for each arrow or WASD key."""
        pg = self.pygame
        return {pg.K_LEFT: (-1, 0), pg.K_a: (-1, 0),
                pg.K_RIGHT: (1, 0), pg.K_d: (1, 0),
                pg.K_UP: (0, -1), pg.K_w: (0, -1),
                pg.K_DOWN: (0, 1), pg.K_s: (0, 1)}

    def run(self):
        """Handle input, update time and the sample, and draw frames until the player quits."""
        while self.running:
            self.update_frame()
            self.clock.tick(60)
        self.pygame.quit()

    async def run_browser(self):
        """Draw frames while giving the browser time to handle input and update the page."""
        while self.running:
            self.update_frame()
            await asyncio.sleep(0)
        self.pygame.quit()

    def update_frame(self):
        """Check the timer, handle input, and draw one frame for either version."""
        self.game.check_bomb()
        if self.game.mode in ("ready", "paused"):
            self.game.demo.tick()
        for event in self.pygame.event.get():
            self.handle_event(event)
        self.game.advance_after_popup()
        self.play_sounds()
        self.buttons = draw_game(self.pygame, self.screen, self.fonts, self.game,
                                 self.sounds.enabled, self.show_help, self.update_effect_age())
        self.pygame.display.flip()

    def update_effect_age(self):
        """Return seconds since the attempt finished, or None while it is not finished.

        The blast shake, the stamp, and the confetti use this to animate.
        """
        if self.game.mode != "finished":
            self.finished_at = None
            return None
        if self.finished_at is None:
            self.finished_at = time.perf_counter()
        return time.perf_counter() - self.finished_at

    def toggle_help(self):
        """Open or close How to play. Opening it during play pauses the countdown first."""
        if not self.show_help and self.game.mode == "playing":
            self.game.toggle_play()
        self.show_help = not self.show_help

    def play_sounds(self):
        """Tick with the countdown, warn on low steps, and mark how an attempt ended.

        The tick speeds up and rises in pitch for the last ten seconds.
        """
        game = self.game
        beat = None
        if game.mode == "playing":
            remaining = game.time_remaining()
            length = 0.5 if remaining <= 10 else 1.0
            beat = (length, math.ceil(remaining / length))
            if self.last_beat is not None and beat != self.last_beat:
                self.sounds.play("fast_tick" if length < 1 else "tick")
        self.last_beat = beat
        warning = game.steps_running_low()
        if warning and not self.warned:
            self.sounds.play("warn")
        self.warned = warning
        if game.level_popup and not self.last_popup:
            self.sounds.play("unlock")
        elif game.mode == "finished" and self.last_mode == "playing":
            if game.passed:
                self.sounds.play("perfect" if game.perfect else "escape")
            else:
                self.sounds.play("blast")
        self.last_mode = game.mode
        self.last_popup = game.level_popup

    def handle_event(self, event):
        """Send keyboard and mouse events to the matching handler, or handle closing the window."""
        pg = self.pygame
        if event.type == pg.QUIT:
            self.running = False
        elif event.type == pg.KEYDOWN:
            self.handle_key(event.key)
        elif event.type == pg.MOUSEBUTTONDOWN and event.button == 1:
            self.handle_mouse_down(event.pos)
        elif event.type == pg.MOUSEMOTION and self.dragging:
            drag_segment(self.game, self.previous_mouse, event.pos)
            self.previous_mouse = event.pos
        elif event.type == pg.MOUSEBUTTONUP and event.button == 1:
            self.dragging = False
        elif event.type == pg.WINDOWFOCUSLOST:
            self.dragging = False

    def handle_key(self, key):
        """Request movement or quit on Escape, unless the completion popup is showing."""
        if key == self.pygame.K_m:
            self.sounds.toggle()
        elif self.game.level_popup:
            return
        elif key in self.key_directions:
            dx, dy = self.key_directions[key]
            self.game.move(dx, dy)
        elif key == self.pygame.K_ESCAPE and sys.platform != "emscripten":
            # In a browser tab there is no window to close, so Escape would
            # only stop the game loop and freeze the page.
            self.running = False

    def handle_mouse_down(self, position):
        """Handle buttons first; during play, start dragging or step toward a tap on the board."""
        self.dragging = False
        if self.click_button(position) or self.game.mode != "playing":
            return
        maze = self.game.maze
        target = screen_position_to_cell(position, maze_geometry(maze))
        if target == self.game.player.position:
            self.dragging = True
            self.previous_mouse = position
        elif 0 <= target[0] < maze.width and 0 <= target[1] < maze.height:
            self.game.move(*step_toward(self.game.player.position, target))

    def click_button(self, position):
        """Return True for a button hit and run its action only if the button is enabled."""
        for button in self.buttons:
            if button.rect.collidepoint(position):
                if button.enabled:
                    self.perform_action(button.action, button.value)
                return True
        return False

    def perform_action(self, action, value):
        """Call the game action requested by a button, or change the visible level page."""
        if action == "level":
            self.game.choose_level(value)
        elif action == "retry":
            self.game.new_attempt()
        elif action == "next":
            self.game.advance()
        elif action == "move":
            dx, dy = value
            self.game.move(dx, dy)
        elif action == "play":
            self.dragging = False
            self.game.toggle_play()
        elif action == "sound":
            self.sounds.toggle()
        elif action == "help":
            self.toggle_help()


# Keep the actual sample class available while tests replace SampleMaze.
REAL_SAMPLE_MAZE = SampleMaze


# ----------------------------------------------------------------------
# TEST HELPERS
# ----------------------------------------------------------------------
# Use a known maze and controllable time to make gameplay tests predictable.

class FakeClock:
    """Provide elapsed time that a test can advance without sleeping."""

    def __init__(self):
        """Start at 100 seconds so a zero start time cannot hide a clock bug."""
        self.now = 100.0

    def __call__(self):
        """Return the current fake time, as time.perf_counter() would."""
        return self.now

    def advance(self, seconds):
        """Advance time; for example, advance(5) adds five seconds."""
        self.now += seconds


class TinyMaze(Maze):
    """Use a known layout while reusing Maze's actual path checks and BFS."""

    def __init__(self, level=0, previous_layout=None):
        """Build a fixed 7 by 7 maze with a three-step nearest exit.

        level and previous_layout are accepted so TinyMaze can replace Maze in tests.
        They are ignored because every test needs the same predictable layout.
        """
        self.width = 7
        self.height = 7
        self.start = (3, 3)
        self.exits = {(0, 1), (6, 5), (3, 6)}
        self.cleared = False
        self.grid = [[1] * self.width for row in range(self.height)]
        for y in range(1, 6):
            for x in range(1, 6):
                self.grid[y][x] = 0
        for x, y in self.exits:
            self.grid[y][x] = 0
        self.shortest_distance = self.find_shortest_distance()


def escape(game, clock=None):
    """Start and take TinyMaze's three downward steps to its nearest exit."""
    game.toggle_play()
    if clock is not None:
        clock.advance(2)
    for step in range(3):
        game.move(0, 1)


# ----------------------------------------------------------------------
# PLAYER TESTS
# ----------------------------------------------------------------------
# Valid moves change state; rejected moves leave it alone.

class PlayerTests(unittest.TestCase):
    """Exercise movement against a fixed maze."""

    def setUp(self):
        """Place the player at the center of an open test maze."""
        self.maze = TinyMaze()
        self.player = Player(self.maze.start)

    def test_valid_move_updates_route_and_steps(self):
        """One rightward move records both cells and exactly one step."""
        self.assertTrue(self.player.move(1, 0, self.maze))
        self.assertEqual(self.player.position, (4, 3))
        self.assertEqual(self.player.path, [(3, 3), (4, 3)])
        self.assertEqual(self.player.steps, 1)

    def test_invalid_moves_leave_state_unchanged(self):
        """Diagonal, zero, multi-cell, and wall moves must all be rejected."""
        self.maze.grid[3][4] = 1
        for direction in [(1, 1), (0, 0), (2, 0), (1, 0)]:
            with self.subTest(direction=direction):
                self.assertFalse(self.player.move(*direction, self.maze))
                self.assertEqual(self.player.position, (3, 3))
                self.assertEqual(self.player.path, [(3, 3)])
                self.assertEqual(self.player.steps, 0)

    def test_retracing_a_cell_still_costs_a_step(self):
        """Moving right then left counts two moves, not zero."""
        self.player.move(1, 0, self.maze)
        self.player.move(-1, 0, self.maze)
        self.assertEqual(self.player.position, self.maze.start)
        self.assertEqual(self.player.steps, 2)
        self.assertEqual(len(self.player.path), 3)


# ----------------------------------------------------------------------
# MAZE TESTS
# ----------------------------------------------------------------------
# Check known BFS distances, generated paths and exits, and fresh wall patterns.

class MazeTests(unittest.TestCase):
    """Test known distances separately from random maze-generation invariants."""

    def test_shortest_distance_chooses_nearest_exit(self):
        """The three exits cost 3, 5, and 5 moves, so BFS must return 3."""
        maze = TinyMaze()
        self.assertEqual(maze.find_shortest_distance(), 3)
        maze.exits.remove((3, 6))
        self.assertEqual(maze.find_shortest_distance(), 5)

    def test_no_reachable_exit_raises_an_error(self):
        """Closing all three exits leaves no legal escape route."""
        maze = TinyMaze()
        for x, y in maze.exits:
            maze.grid[y][x] = 1
        with self.assertRaises(ValueError):
            maze.find_shortest_distance()

    def test_outside_cells_and_walls_are_not_open(self):
        """Boundary checks reject negative and oversized coordinates."""
        maze = TinyMaze()
        for position in [(-1, 1), (1, -1), (7, 1), (1, 7), (0, 0)]:
            self.assertFalse(maze.is_open(*position))
        self.assertTrue(maze.is_open(3, 3))
        self.assertTrue(maze.is_open(3, 6))

    def test_generated_levels_have_connected_paths_and_three_exits(self):
        """Levels 1, 50, and 100 keep reachable edge exits and an interior start."""
        for level in [0, 49, 99]:
            with self.subTest(level=level):
                with patch(__name__ + '.random', random.Random(200 + level)):
                    maze = Maze(level)
                distances = maze.distances_from_start()
                open_cells = sum(row.count(0) for row in maze.grid)
                self.assertEqual(len(distances), open_cells)
                self.assertEqual(len(maze.exits), 3)
                self.assertEqual(maze.shortest_distance,
                                 min(distances[exit_cell] for exit_cell in maze.exits))
                self.assertTrue(0 < maze.start[0] < maze.width - 1)
                self.assertTrue(0 < maze.start[1] < maze.height - 1)
                for x, y in maze.exits:
                    self.assertTrue(x in (0, maze.width - 1) or y in (0, maze.height - 1))

    def test_new_layout_differs_from_previous(self):
        """A fresh same-level maze must not reuse the previous wall arrangement."""
        with patch(__name__ + '.random', random.Random(321)):
            first = Maze(0)
            second = Maze(0, first.get_wall_pattern())
        self.assertNotEqual(first.get_wall_pattern(), second.get_wall_pattern())
        self.assertEqual((first.width, first.height), (second.width, second.height))


# ----------------------------------------------------------------------
# BFS AND DFS TESTS
# ----------------------------------------------------------------------
# Check found paths, the display delay, and switching between search methods.

class DemoTests(unittest.TestCase):
    """Run the actual BFS/DFS logic on a small, independent sample."""

    def setUp(self):
        """Use a one-exit sample and a clock controlled by each test."""
        self.clock = FakeClock()
        clock_patch = patch(__name__ + '.time.perf_counter', self.clock)
        maze_patch = patch(__name__ + '.SampleMaze', TinyMaze)
        self.addCleanup(clock_patch.stop)
        self.addCleanup(maze_patch.stop)
        clock_patch.start()
        maze_patch.start()
        self.search = DemoSearch()
        self.search.maze.exits = {(3, 6)}

    def search_until_found(self):
        """Allow at most 100 ticks before reporting a broken search."""
        for tick in range(100):
            self.search.tick()
            if self.search.found:
                return
            self.clock.advance(0.05)
        self.fail('Search never reached the exit.')

    def assert_legal_path(self):
        """The recovered path must connect the sample start to an exit legally."""
        path = self.search.path
        self.assertEqual(path[0], self.search.maze.start)
        self.assertIn(path[-1], self.search.maze.exits)
        for first, second in zip(path, path[1:]):
            self.assertTrue(self.search.maze.is_open(*second))
            self.assertEqual(abs(first[0] - second[0]) + abs(first[1] - second[1]), 1)

    def test_bfs_finds_a_shortest_route(self):
        """BFS's recovered route length equals the sample's shortest distance."""
        self.search_until_found()
        self.assert_legal_path()
        self.assertEqual(len(self.search.path) - 1,
                         self.search.maze.find_shortest_distance())

    def test_path_is_held_then_dfs_finds_a_legal_route(self):
        """BFS shows its path for three seconds, then DFS searches the same sample."""
        self.search_until_found()
        path = self.search.path.copy()
        self.clock.advance(2.9)
        self.search.tick()
        self.assertEqual(self.search.method, 'BFS')
        self.assertEqual(self.search.path, path)
        self.clock.advance(0.2)
        self.search.tick()
        self.assertEqual(self.search.method, 'DFS')
        self.assertEqual(self.search.path, [])
        self.search_until_found()
        self.assert_legal_path()
        self.assertEqual(len(self.search.checked_cells), len(set(self.search.checked_cells)))
        self.clock.advance(3)
        self.search.tick()
        self.assertEqual(self.search.method, 'BFS')

    def test_real_sample_uses_level_100_size_and_one_exit(self):
        """The waiting screen keeps its dense sample and one reachable exit."""
        maze = REAL_SAMPLE_MAZE()
        self.assertEqual((maze.width, maze.height), (67, 49))
        self.assertEqual(len(maze.exits), 1)
        self.assertGreater(maze.find_shortest_distance(), 0)


# ----------------------------------------------------------------------
# GAME RULE TESTS
# ----------------------------------------------------------------------
# Check timing, points, retries, progression, recovery, and the final level.

class GameTests(unittest.TestCase):
    """Check observable game behavior using fixed layouts and time."""

    def setUp(self):
        """Replace only maze generation and the clock; run the actual Game rules."""
        self.clock = FakeClock()
        clock_patch = patch(__name__ + '.time.perf_counter', self.clock)
        maze_patch = patch(__name__ + '.Maze', TinyMaze)
        self.addCleanup(clock_patch.stop)
        self.addCleanup(maze_patch.stop)
        clock_patch.start()
        maze_patch.start()
        self.game = Game()

    def test_ready_screen_does_not_consume_time_or_allow_movement(self):
        """Waiting before Start is free and leaves the player at the start."""
        self.clock.advance(1000)
        self.game.move(0, 1)
        self.assertEqual(self.game.mode, 'ready')
        self.assertEqual(self.game.elapsed_time(), 0)
        self.assertEqual(self.game.player.steps, 0)
        self.assertFalse(self.game.check_bomb())
        self.assertEqual(self.game.total_score, 0)

    def test_pause_holds_timer_position_and_route(self):
        """Paused time and attempted paused moves cannot alter an attempt."""
        self.game.toggle_play()
        self.clock.advance(5)
        self.game.move(1, 0)
        self.game.toggle_play()
        saved_path = self.game.player.path.copy()
        remaining = self.game.time_remaining()
        self.clock.advance(1000)
        self.game.move(0, 1)
        self.assertEqual(self.game.mode, 'paused')
        self.assertEqual(self.game.time_remaining(), remaining)
        self.assertEqual(self.game.player.path, saved_path)
        self.game.toggle_play()
        self.clock.advance(3)
        self.assertEqual(self.game.elapsed_time(), 8)

    def test_timeout_at_exact_zero_is_charged_once(self):
        """Pausing at the deadline cannot prevent or duplicate the explosion."""
        self.game.toggle_play()
        self.clock.advance(self.game.bomb_seconds)
        self.assertFalse(self.game.toggle_play())
        self.assertEqual(self.game.failure_reason, 'main')
        self.assertEqual(self.game.mode, 'finished')
        self.assertFalse(self.game.check_bomb())
        self.assertEqual(self.game.total_score, -100)
        self.assertEqual(self.game.level_points[0], -100)
        self.assertEqual(self.game.failures[0], 1)

    def test_step_overflow_explodes_before_any_exit(self):
        """At the allowance the player is safe; the next valid move explodes."""
        self.game.toggle_play()
        for direction in [(1, 0), (-1, 0), (1, 0)]:
            self.game.move(*direction)
        self.assertEqual(self.game.player.steps, self.game.step_limit)
        self.assertEqual(self.game.mode, 'playing')
        self.game.move(-1, 0)
        self.assertNotIn(self.game.player.position, self.game.maze.exits)
        self.assertEqual(self.game.mode, 'finished')
        self.assertEqual(self.game.failure_reason, 'steps')
        self.assertEqual(self.game.total_score, -33)
        self.assertEqual(self.game.failures[0], 1)

    def test_low_step_warning_only_shows_during_an_attempt(self):
        """TinyMaze's limit of 3 is already close, but only while playing or paused."""
        self.assertFalse(self.game.steps_running_low())
        self.game.toggle_play()
        self.assertTrue(self.game.steps_running_low())
        for step in range(3):
            self.game.move(0, 1)
        self.assertEqual(self.game.mode, 'finished')
        self.assertFalse(self.game.steps_running_low())

    def test_tip_changes_after_each_passed_maze(self):
        """One tip shows at a time and the next appears after a pass."""
        first = current_tip(self.game)
        escape(self.game)
        self.assertNotEqual(current_tip(self.game), first)

    def test_live_and_paused_retries_keep_layout_and_cost_points(self):
        """Each abandoned attempt costs once and returns the same maze to ready."""
        maze = self.game.maze
        for pause in [False, True]:
            self.game.toggle_play()
            self.game.move(1, 0)
            if pause:
                self.game.toggle_play()
            self.assertTrue(self.game.new_attempt())
            self.assertIs(self.game.maze, maze)
            self.assertEqual(self.game.mode, 'ready')
            self.assertEqual(self.game.player.position, maze.start)
            self.assertEqual(self.game.player.steps, 0)
        self.assertEqual(self.game.total_score, -200)
        self.assertEqual(self.game.level_points[0], -200)
        self.game.new_attempt()
        self.assertEqual(self.game.total_score, -200)

    def test_success_excludes_paused_time_and_rewards_shortest_route(self):
        """A pause adds no elapsed time; the exact route earns the perfect bonus."""
        self.game.toggle_play()
        self.clock.advance(2)
        self.game.toggle_play()
        self.clock.advance(1000)
        self.game.toggle_play()
        for step in range(3):
            self.game.move(0, 1)
        expected = escape_points(3, 3, 43, 45) + PERFECT_BONUS
        self.assertTrue(self.game.passed)
        self.assertTrue(self.game.perfect)
        self.assertEqual(self.game.final_time, 2)
        self.assertEqual(self.game.attempt_score, expected)
        self.assertEqual(self.game.solved_counts[0], 1)

    def test_replaying_cleared_maze_cannot_farm_points(self):
        """Retrying a passed maze grants neither another pass nor more points."""
        escape(self.game)
        score = self.game.total_score
        self.game.new_attempt()
        escape(self.game)
        self.assertEqual(self.game.total_score, score)
        self.assertEqual(self.game.solved_counts[0], 1)
        maze = self.game.maze
        self.assertTrue(self.game.advance())
        self.assertIsNot(self.game.maze, maze)
        self.assertEqual(self.game.mode, 'ready')

    def test_gate_requires_quota_net_level_points_and_nonnegative_total(self):
        """Check all three requirements and the exact 5,000-point boundary."""
        cases = [(9, 5000, 5000, False), (10, 4999, 99999, False),
                 (10, 5000, -1, False), (10, 5000, 0, True)]
        for count, points, total, expected in cases:
            with self.subTest(count=count, points=points, total=total):
                self.game.solved_counts[0] = count
                self.game.level_points[0] = points
                self.game.total_score = total
                self.assertEqual(self.game.level_ready(), expected)

    def test_tenth_reward_is_posted_before_checking_unlock(self):
        """Exactly 5,000 after the tenth reward unlocks the next level."""
        self.game.solved_counts[0] = 9
        self.game.level_points[0] = 3750
        self.game.total_score = 3750
        escape(self.game)
        self.assertEqual(self.game.level_points[0], 5000)
        self.assertEqual(self.game.highest_unlocked_level, 1)
        self.assertTrue(self.game.level_popup)
        self.assertFalse(self.game.advance_after_popup())
        self.clock.advance(1.2)
        self.assertTrue(self.game.advance_after_popup())
        self.assertEqual(self.game.level, 1)
        self.assertEqual(self.game.mode, 'ready')
        self.assertEqual(self.game.level_points[1], 0)

    def test_extra_mazes_earn_shortfall_without_increasing_quota(self):
        """A tenth pass one point short stays at this level until more is earned."""
        self.game.solved_counts[0] = 9
        self.game.level_points[0] = 3749
        self.game.total_score = 3749
        escape(self.game)
        self.assertFalse(self.game.level_ready())
        self.assertFalse(self.game.level_popup)
        self.game.advance()
        self.assertEqual(self.game.level, 0)
        escape(self.game)
        self.assertEqual(self.game.solved_counts[0], MAZES_PER_LEVEL)
        self.assertTrue(self.game.level_ready())

    def test_lockout_requires_previous_level_recovery(self):
        """Three failures lock level 2 until a fresh level-1 pass restores access."""
        self.game.solved_counts[0] = 10
        self.game.level_points[0] = LEVEL_POINTS_REQUIRED
        self.game.total_score = LEVEL_POINTS_REQUIRED
        self.game.highest_unlocked_level = 1
        self.assertTrue(self.game.choose_level(1))
        for attempt in range(3):
            self.game.toggle_play()
            self.game.new_attempt()
        self.assertEqual(self.game.highest_unlocked_level, 0)
        self.assertFalse(self.game.new_attempt())
        self.assertTrue(self.game.choose_level(0))
        escape(self.game)
        self.assertEqual(self.game.highest_unlocked_level, 1)
        self.assertEqual(self.game.failures[1], 0)

    def test_selecting_active_level_is_free_but_leaving_live_level_costs(self):
        """Clicking the current number is a no-op; leaving level 2 costs once."""
        self.game.highest_unlocked_level = 1
        self.game.solved_counts[0] = 10
        self.game.level_points[0] = 5000
        self.game.total_score = 5000
        self.game.choose_level(1)
        self.game.toggle_play()
        self.assertFalse(self.game.choose_level(1))
        self.assertEqual(self.game.total_score, 5000)
        self.assertTrue(self.game.choose_level(0))
        self.assertEqual(self.game.total_score, 4900)
        self.assertEqual(self.game.level_points[1], -100)
        self.assertEqual(self.game.failures[1], 1)

    def test_final_level_does_not_advance_to_101(self):
        """Completing level 100 celebrates without attempting another index."""
        self.game.highest_unlocked_level = 99
        self.game.solved_counts[0] = 10
        self.game.level_points[0] = 5000
        self.game.total_score = 5000
        self.game.choose_level(99)
        self.game.solved_counts[99] = 9
        self.game.level_points[99] = 3750
        escape(self.game)
        self.assertTrue(self.game.level_popup)
        self.clock.advance(2)
        self.game.advance_after_popup()
        self.assertEqual(self.game.level, 99)
        self.assertFalse(self.game.advance())


# ----------------------------------------------------------------------
# INTERFACE TESTS
# ----------------------------------------------------------------------
# Check input and sample-only drawing while ready or paused. Pygame uses
# an offscreen display; these tests are skipped when pygame is unavailable.

@unittest.skipIf(pygame is None, 'Install pygame==2.6.1 to run the interface tests.')
class InterfaceTests(unittest.TestCase):
    """Check input dispatch and ensure pauses do not reveal the real board."""

    def setUp(self):
        """Create an offscreen display and tiny real maze for each test."""
        pygame.init()
        self.addCleanup(pygame.quit)
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        self.fonts = make_fonts(pygame)
        maze_patch = patch(__name__ + '.Maze', TinyMaze)
        self.addCleanup(maze_patch.stop)
        maze_patch.start()
        self.game = Game()

    def test_ready_and_paused_render_only_the_sample(self):
        """Only active play may pass the real maze to the board renderer."""
        for mode in ['ready', 'playing', 'paused']:
            if mode != 'ready':
                self.game.toggle_play()
            with patch(__name__ + '.draw_maze') as draw_maze:
                draw_game(pygame, self.screen, self.fonts, self.game)
            expected = self.game.maze if mode == 'playing' else self.game.demo.maze
            self.assertEqual(draw_maze.call_count, 1)
            self.assertIs(draw_maze.call_args.args[2], expected)

    def test_named_buttons_start_pause_resume_and_ignore_disabled_levels(self):
        """Real click handling uses Button fields and respects enabled state."""
        app = self.make_app()
        for expected_mode in ['playing', 'paused', 'playing']:
            app.buttons = make_buttons(pygame, self.game)
            button = next(button for button in app.buttons if button.action == 'play')
            self.assertTrue(app.click_button(button.rect.center))
            self.assertEqual(self.game.mode, expected_mode)
        app.buttons = make_buttons(pygame, self.game)
        locked = next(button for button in app.buttons if not button.enabled)
        self.assertTrue(app.click_button(locked.rect.center))
        self.assertEqual(self.game.level, 0)
        self.assertEqual(self.game.total_score, 0)

    def test_keyboard_and_drag_share_the_movement_rules(self):
        """W uses Game.move; a drag cannot move the player while paused."""
        app = self.make_app()
        self.game.toggle_play()
        app.handle_key(pygame.K_w)
        self.assertEqual(self.game.player.position, (3, 2))
        geometry = maze_geometry(self.game.maze)
        before = cell_center((3, 2), geometry)
        after = cell_center((4, 2), geometry)
        drag_segment(self.game, before, after)
        self.assertEqual(self.game.player.position, (4, 2))
        self.game.toggle_play()
        drag_segment(self.game, after, before)
        self.assertEqual(self.game.player.position, (4, 2))

    def test_tapping_the_board_steps_once_toward_the_tap(self):
        """A tap far from the player moves one cell; taps off the board do nothing."""
        app = self.make_app()
        self.game.toggle_play()
        geometry = maze_geometry(self.game.maze)
        app.handle_mouse_down(cell_center((5, 4), geometry))
        self.assertEqual(self.game.player.position, (4, 3))
        app.handle_mouse_down((5, 5))
        self.assertEqual(self.game.player.position, (4, 3))

    def test_sound_button_and_m_key_toggle_sound(self):
        """The Sound button and M both mute and unmute, and the label follows."""
        app = self.make_app()
        button = next(button for button in make_buttons(pygame, self.game)
                      if button.action == 'sound')
        self.assertEqual(button.label, 'Sound: on')
        app.buttons = [button]
        app.click_button(button.rect.center)
        self.assertFalse(app.sounds.enabled)
        muted = make_buttons(pygame, self.game, app.sounds.enabled)
        self.assertIn('Sound: off', [button.label for button in muted])
        app.handle_key(pygame.K_m)
        self.assertTrue(app.sounds.enabled)

    def test_help_button_pauses_play_and_closes_again(self):
        """Opening How to play during an attempt pauses it; Got it! closes the panel."""
        app = self.make_app()
        self.game.toggle_play()
        app.perform_action("help", 0)
        self.assertTrue(app.show_help)
        self.assertEqual(self.game.mode, "paused")
        buttons = draw_game(pygame, self.screen, self.fonts, self.game, show_help=True)
        self.assertEqual([button.action for button in buttons], ["help"])
        app.perform_action("help", 0)
        self.assertFalse(app.show_help)

    def make_app(self):
        """Use App's real input methods without opening its scaled window."""
        app = App.__new__(App)
        app.pygame = pygame
        app.game = self.game
        app.dragging = False
        app.running = True
        app.buttons = []
        app.key_directions = app.make_key_directions()
        app.sounds = Sounds(pygame)
        app.show_help = False
        app.finished_at = None
        return app


# ----------------------------------------------------------------------
# TEST RUNNER AND PROGRAM START
# ----------------------------------------------------------------------


def run_tests():
    """Run docstring examples and behavior tests; return 0 on success or 1 on failure."""
    os.environ['SDL_VIDEODRIVER'] = 'dummy'
    os.environ['SDL_AUDIODRIVER'] = 'dummy'
    module = sys.modules[__name__]
    suite = unittest.TestSuite()
    suite.addTests(doctest.DocTestSuite(module))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromModule(module))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def main():
    """Play normally, show --help, or run the tests with --test."""
    if '--help' in sys.argv[1:] or '-h' in sys.argv[1:]:
        print(__doc__)
        return 0
    if '--test' in sys.argv[1:]:
        return run_tests()
    if pygame is None:
        print('Install pygame inside your virtual environment:')
        print('python -m pip install pygame==2.6.1')
        return 1
    app = App()
    app.run()
    return 0


if __name__ == '__main__':
    sys.exit(main())
