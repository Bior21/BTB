#!/usr/bin/env python3
"""Beat the Blast

Find your way out of a maze before the bomb explodes. Reach any gold exit
before time runs out, and avoid unnecessary steps, which can also trigger
an explosion.

Press Start to begin. Drag the blue player or use the arrow keys or WASD
to move. Pause stops the countdown and hides the maze until you resume.

Pass ten mazes and earn enough points to unlock the next level.
There are 100 levels to complete.
"""

import doctest
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
WINDOW_HEIGHT = 810
BACKGROUND = (21, 34, 31)
WALL = (53, 73, 63)
CORRIDOR = (16, 26, 24)
TEXT = (237, 242, 235)
MUTED = (181, 198, 187)
BLUE = (159, 216, 229)
GOLD = (232, 200, 140)
ORANGE = (224, 164, 126)
GREEN = (195, 223, 139)


# ----------------------------------------------------------------------
# BUTTON DESCRIPTIONS
# ----------------------------------------------------------------------
# A Button describes a control. Drawing paints it; App handles its action.

class Button:
    """Keep a button's appearance, action, and availability together."""

    def __init__(self, *, label, rect, action, value=0, enabled=True):
        """Store a button's label, area, action, and whether it can be clicked.

        >>> button = Button(label="New attempt", rect=None, action="retry")
        >>> button.label, button.action, button.enabled
        ('New attempt', 'retry', True)
        """
        self.label = label
        self.rect = rect
        self.action = action
        self.value = value
        self.enabled = enabled


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
        self.level_page = 0
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
        self.level_page = level // 10
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

def maze_geometry(maze):
    """Return (left, top, cell_size) to fit and center this maze in the board area."""
    cell_size = min(710 // maze.width, 404 // maze.height)
    left = 220 + (710 - maze.width * cell_size) // 2
    top = 232 + (404 - maze.height * cell_size) // 2
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

def draw_text(screen, font, text, position, color=TEXT):
    """Draw text at the given pixel position."""
    screen.blit(font.render(text, True, color), position)


def draw_wrapped_text(screen, font, text, x, y, width, color=TEXT):
    """Draw text one word at a time, starting a new line when the width is exceeded."""
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


def make_buttons(pygame, game):
    """Return level, attempt, and movement button descriptions for this frame."""
    buttons = make_level_buttons(pygame, game)
    buttons.extend(make_attempt_buttons(pygame, game))
    labels = ["<", "^", "v", ">"]
    directions = [(-1, 0), (0, -1), (0, 1), (1, 0)]
    for index, (label, direction) in enumerate(zip(labels, directions)):
        rect = pygame.Rect(704 + index * 55, 737, 46, 42)
        buttons.append(Button(label=label, rect=rect, action="move",
                              value=direction, enabled=game.mode != "finished"))
    return buttons


def make_level_buttons(pygame, game):
    """Build ten level buttons and page arrows, enabling only allowed level choices."""
    buttons = []
    for offset in range(10):
        index = game.level_page * 10 + offset
        rect = pygame.Rect(82 + offset * 79, 182, 73, 34)
        enabled = index <= game.highest_unlocked_level and (index <= game.level or game.level_ready())
        buttons.append(Button(label=f"Level {index + 1}", rect=rect,
                              action="level", value=index, enabled=enabled))
    buttons.append(Button(label="<", rect=pygame.Rect(30, 182, 42, 34),
                          action="page", value=-1, enabled=game.level_page > 0))
    buttons.append(Button(label=">", rect=pygame.Rect(888, 182, 42, 34),
                          action="page", value=1, enabled=game.level_page < 9))
    return buttons


def make_attempt_buttons(pygame, game):
    """Build retry, play, advance, and previous-level recovery controls from the game state."""
    retry_rect = pygame.Rect(162, 737, 155, 42)
    next_rect = pygame.Rect(329, 737, 135, 42)
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
        rect = pygame.Rect(476, 737, 165, 42)
        buttons.append(Button(label="Previous level", rect=rect,
                              action="level", value=game.level - 1))
    return buttons


def make_play_button(pygame, game, can_retry):
    """Return the Start, Pause, or Resume button for the current attempt mode."""
    labels = {"ready": "Start", "playing": "Pause", "paused": "Resume", "finished": "Start"}
    return Button(label=labels[game.mode], rect=pygame.Rect(30, 737, 120, 42),
                  action="play", enabled=can_retry and game.mode != "finished")


def draw_game(pygame, screen, fonts, game):
    """Draw the current screen and return its clickable button descriptions."""
    screen.fill(BACKGROUND)
    draw_heading(pygame, screen, fonts, game)
    draw_statistics(pygame, screen, fonts, game)
    draw_board(pygame, screen, fonts, game)
    draw_messages(screen, fonts, game)
    buttons = make_buttons(pygame, game)
    for button in buttons:
        draw_button(pygame, screen, fonts[2], game, button)
    if game.level_popup:
        buttons = draw_level_popup(pygame, screen, fonts, game)
    return buttons


def draw_board(pygame, screen, fonts, game):
    """Show the separate sample while ready or paused, and the real maze otherwise."""
    if game.mode in ("ready", "paused"):
        draw_sample(pygame, screen, fonts, game)
        return
    geometry = maze_geometry(game.maze)
    draw_maze(pygame, screen, game.maze, geometry)
    draw_player_path(pygame, screen, game, geometry)
    draw_player_and_exits(pygame, screen, game, geometry)
    draw_blast_effect(pygame, screen, game, geometry)


def draw_sample(pygame, screen, fonts, game):
    """Draw the sample maze, checked cells, found path, and BFS or DFS label."""
    demo = game.demo
    size = min(710 // demo.maze.width, 372 // demo.maze.height)
    geometry = (220 + (710 - demo.maze.width * size) // 2, 272, size)
    pygame.draw.rect(screen, (40, 64, 56), pygame.Rect(485, 232, 180, 28), border_radius=4)
    draw_centered_text(screen, fonts[2], f"{demo.method} SEARCH", (575, 246))
    draw_maze(pygame, screen, demo.maze, geometry)
    for x, y in demo.checked_cells:
        rect = pygame.Rect(geometry[0] + x * size + 2, geometry[1] + y * size + 2, size - 4, size - 4)
        pygame.draw.rect(screen, (43, 82, 70), rect)
    draw_demo_path(pygame, screen, demo, geometry)
    for position in demo.maze.exits:
        pygame.draw.circle(screen, GOLD, cell_center(position, geometry), max(3, size // 4))
    pygame.draw.circle(screen, BLUE, cell_center(demo.current, geometry), max(3, size // 5))


def draw_demo_path(pygame, screen, demo, geometry):
    """Draw the sample search's found path in green once an exit has been reached."""
    if not demo.found or len(demo.path) < 2:
        return
    points = [cell_center(position, geometry) for position in demo.path]
    pygame.draw.lines(screen, GREEN, False, points, max(2, geometry[2] // 4))


def draw_centered_text(screen, font, text, center, color=TEXT):
    """Draw text centered on the requested pixel position."""
    image = font.render(text, True, color)
    screen.blit(image, image.get_rect(center=center))


def draw_popup_badge(pygame, screen):
    """Draw a gold circle with a dark check mark above the completion message."""
    pygame.draw.circle(screen, GOLD, (480, 301), 27)
    pygame.draw.lines(screen, BACKGROUND, False, [(467, 301), (477, 310), (494, 291)], 4)


def draw_level_popup(pygame, screen, fonts, game):
    """Draw the level celebration and return no buttons while it covers the screen."""
    shade = pygame.Surface(screen.get_size(), pygame.SRCALPHA)
    shade.fill((9, 18, 14, 175))
    screen.blit(shade, (0, 0))
    pygame.draw.rect(screen, (10, 20, 16), pygame.Rect(276, 251, 420, 190), border_radius=22)
    pygame.draw.rect(screen, (43, 65, 54), pygame.Rect(270, 245, 420, 190), border_radius=22)
    draw_popup_badge(pygame, screen)
    draw_centered_text(screen, fonts[0], f"Level {game.level + 1} passed!", (480, 357))
    subtitle = f"Level {game.level + 2} unlocked!"
    if game.level == len(LEVELS) - 1:
        subtitle = "All 100 levels complete!"
    draw_centered_text(screen, fonts[1], subtitle, (480, 392), GREEN)
    return []


def draw_heading(pygame, screen, fonts, game):
    """Draw the game title, level progress, and indented instructions."""
    title_font, font, small_font = fonts
    draw_text(screen, title_font, "BEAT THE BLAST", (30, 20))
    maze_number = min(MAZES_PER_LEVEL, game.solved_counts[game.level] + (not game.maze.cleared))
    progress = f"Level {game.level + 1}/100 · Maze {maze_number}/10"
    draw_text(screen, small_font, progress, (650, 28), MUTED)
    draw_text(screen, font, "Instructions", (30, 61))
    instructions = ["Drag or use arrows / WASD. Blue: you · Gold: any exit.",
                    "Start when ready. Pause hides your maze and freezes the countdown.",
                    "Escape before the bomb countdown reaches zero.",
                    "Exceed the hidden step limit and the bomb explodes immediately.",
                    "Unlock: 10 mazes + 5,000 net level points. Live restarts cost 100 points and a failure."]
    for index, instruction in enumerate(instructions):
        draw_instruction(pygame, screen, small_font, instruction, 85 + index * 18)


def draw_instruction(pygame, screen, font, text, top):
    """Draw one instruction beside its four-diamond bullet."""
    for dx, dy in [(0, -3), (-3, 0), (3, 0), (0, 3)]:
        x, y = 56 + dx, top + 7 + dy
        points = [(x, y - 2), (x + 2, y), (x, y + 2), (x - 2, y)]
        pygame.draw.polygon(screen, MUTED, points)
    draw_text(screen, font, text, (70, top), MUTED)


def draw_statistics(pygame, screen, fonts, game):
    """Draw countdown, steps, points, and failure counts in the left sidebar."""
    remaining = math.ceil(game.time_remaining() * 10) / 10
    countdown = "Ready" if game.mode == "ready" else f"{remaining:.1f}s"
    values = [("Bomb countdown", countdown),
              ("Steps", str(game.player.steps)),
              ("Points", f"{game.total_score:+d}"),
              ("Negative finishes", f"{game.failures[game.level]} / {LOCK_AFTER_FAILURES}")]
    for index, (label, value) in enumerate(values):
        rect = pygame.Rect(30, 232 + index * 98, 170, 82)
        color = ORANGE if label == "Bomb countdown" and remaining <= 10 else TEXT
        draw_stat_box(pygame, screen, fonts, rect, label, value, color)
        if label == "Points":
            detail = f"Level {game.level_points[game.level]:,} / {LEVEL_POINTS_REQUIRED:,}"
            draw_text(screen, fonts[2], detail, (rect.x + 12, rect.y + 63), MUTED)


def draw_stat_box(pygame, screen, fonts, rect, label, value, value_color=TEXT):
    """Draw a statistic label above its value, such as Bomb countdown above 12.4s."""
    pygame.draw.rect(screen, (40, 64, 56), rect, border_radius=4)
    draw_text(screen, fonts[2], label, (rect.x + 12, rect.y + 12), MUTED)
    draw_text(screen, fonts[1], value, (rect.x + 12, rect.y + 42), value_color)


def draw_blast_effect(pygame, screen, game, geometry):
    """Draw a static burst around the player after an explosion, clipped to the maze."""
    if game.failure_reason is None:
        return
    previous_clip = screen.get_clip()
    left, top, size = geometry
    screen.set_clip(pygame.Rect(left, top, game.maze.width * size, game.maze.height * size))
    x, y = cell_center(game.player.position, geometry)
    radius = max(12, geometry[2])
    pygame.draw.circle(screen, ORANGE, (x, y), radius, 3)
    for index in range(8):
        angle = index * math.pi / 4
        inner = (x + math.cos(angle) * radius * 1.4, y + math.sin(angle) * radius * 1.4)
        outer = (x + math.cos(angle) * radius * 1.9, y + math.sin(angle) * radius * 1.9)
        pygame.draw.line(screen, GOLD, inner, outer, 2)
    screen.set_clip(previous_clip)


def draw_maze(pygame, screen, maze, geometry):
    """Draw each grid cell as either a wall or an open path."""
    left, top, size = geometry
    for y, row in enumerate(maze.grid):
        for x, wall in enumerate(row):
            rect = pygame.Rect(left + x * size, top + y * size, size, size)
            pygame.draw.rect(screen, WALL if wall else CORRIDOR, rect)


def draw_player_path(pygame, screen, game, geometry):
    """Draw the route the player actually traveled.

    A shortest-route finish turns that same route green. The game does not draw
    a suggested solution, since finding the route is the challenge.
    """
    if len(game.player.path) < 2:
        return
    points = []
    for position in game.player.path:
        points.append(cell_center(position, geometry))
    color = GREEN if game.perfect else ORANGE
    pygame.draw.lines(screen, color, False, points, max(2, geometry[2] // 7))


def draw_player_and_exits(pygame, screen, game, geometry):
    """Draw gold exit squares and the blue player over the maze."""
    size = geometry[2]
    for position in game.maze.exits:
        marker_size = max(3, size // 2)
        exit_rect = pygame.Rect(0, 0, marker_size, marker_size)
        exit_rect.center = cell_center(position, geometry)
        pygame.draw.rect(screen, GOLD, exit_rect)
    player_center = cell_center(game.player.position, geometry)
    pygame.draw.circle(screen, BLUE, player_center, max(2, size // 4))


def draw_messages(screen, fonts, game):
    """Draw the attempt message and, after a finish, its score and active time."""
    if game.level_complete_notice:
        return
    message = game.message
    if game.mode == "finished":
        message += f" Score: {game.attempt_score:+d}. Time: {game.final_time:.1f}s."
    color = ORANGE if game.failure_reason else (GREEN if game.perfect else TEXT)
    draw_wrapped_text(screen, fonts[1], message, 220, 656, 710, color)


def draw_button(pygame, screen, font, game, button):
    """Draw a button using its label, area, enabled state, and level selection."""
    fill = (40, 64, 56) if button.enabled else (31, 43, 39)
    if button.action == "level" and button.value == game.level:
        fill = (71, 95, 65)
    pygame.draw.rect(screen, fill, button.rect, border_radius=4)
    ink = TEXT if button.enabled else (109, 124, 114)
    text = font.render(button.label, True, ink)
    screen.blit(text, text.get_rect(center=button.rect.center))


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
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT), pygame.SCALED)
        pygame.display.set_caption("Beat the Blast")
        self.fonts = (pygame.font.Font(None, 34), pygame.font.Font(None, 23), pygame.font.Font(None, 20))
        self.clock = pygame.time.Clock()
        pygame.key.set_repeat(160, 90)
        self.game = Game()
        self.buttons = []
        self.dragging = False
        self.previous_mouse = None
        self.running = True
        self.key_directions = self.make_key_directions()

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
            self.game.check_bomb()
            if self.game.mode in ("ready", "paused"):
                self.game.demo.tick()
            for event in self.pygame.event.get():
                self.handle_event(event)
            self.game.advance_after_popup()
            self.buttons = draw_game(self.pygame, self.screen, self.fonts, self.game)
            self.pygame.display.flip()
            self.clock.tick(60)
        self.pygame.quit()

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
        if self.game.level_popup:
            return
        if key in self.key_directions:
            dx, dy = self.key_directions[key]
            self.game.move(dx, dy)
        elif key == self.pygame.K_ESCAPE:
            self.running = False

    def handle_mouse_down(self, position):
        """Handle buttons first; during play, start dragging or request a neighboring move."""
        self.dragging = False
        if self.click_button(position) or self.game.mode != "playing":
            return
        target = screen_position_to_cell(position, maze_geometry(self.game.maze))
        if target == self.game.player.position:
            self.dragging = True
            self.previous_mouse = position
        else:
            x, y = self.game.player.position
            self.game.move(target[0] - x, target[1] - y)

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
        elif action == "page":
            self.game.level_page = min(9, max(0, self.game.level_page + value))
        elif action == "play":
            self.dragging = False
            self.game.toggle_play()


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
        self.screen = pygame.display.set_mode((960, 810))
        self.fonts = (pygame.font.Font(None, 34), pygame.font.Font(None, 23),
                      pygame.font.Font(None, 20))
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

    def make_app(self):
        """Use App's real input methods without opening its scaled window."""
        app = App.__new__(App)
        app.pygame = pygame
        app.game = self.game
        app.dragging = False
        app.running = True
        app.buttons = []
        app.key_directions = app.make_key_directions()
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
