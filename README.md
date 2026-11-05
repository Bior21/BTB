# Beat the Blast

Beat the Blast (BTB) is a maze escape game where you race against a bomb countdown. You need to reach an exit before time runs out, but speed alone is not enough. Taking too many steps also sets off the bomb, so you have to think carefully about which way to go.

## How to play

- Press **Start** to reveal the maze and begin the countdown.
- Move the yellow player by dragging it, tapping the maze, using the arrow keys or WASD, or clicking the arrow buttons.
- Reach any green flag before the bomb's fuse burns out, without taking too many steps.
- Earn more points by escaping quickly and choosing a shorter route.
- Use **Pause** when you need a break. It stops the countdown and hides your maze until you resume.
- Complete 10 different mazes and earn enough points to unlock the next level. There are 100 levels.

## Tools and techniques

- **Python:** The entire game is written in Python.
- **pygame:** I used pygame to draw the maze and buttons and handle keyboard and mouse input.
- **Breadth-first search (BFS):** I used BFS to find the fewest steps needed to reach an exit. It checks places one step away, then two steps away, and so on until it reaches an exit. This distance helps determine the step limit, countdown, and score.
- **Depth-first search (DFS):** I used DFS to build the maze’s paths. It follows one path as far as possible, then goes back to try another direction when it cannot continue.
- **Random maze generation:** The game creates new mazes by choosing random directions during DFS, then opening extra connections to give players alternative routes. It also chooses a random starting position and compares possible exit locations to make the choice less obvious. Later levels use larger mazes and aim for longer escape routes.
- **Fonts:** [Bangers](https://fonts.google.com/specimen/Bangers) and [Nunito](https://fonts.google.com/specimen/Nunito), both under the SIL Open Font License (see the `fonts` folder).
