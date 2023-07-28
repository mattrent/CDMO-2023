int: R; % number of rows
int: C; % number of columns
set of int: HEIGHT = 1..R;
set of int: WIDTH = 1..C;
array [HEIGHT,WIDTH] of int: grid;

array [HEIGHT, WIDTH] of var int: walls_grid; % computed grid of 0 (free cells) and 1 (walls)

% TODO: define a predicate for "walled cell" given coordinates and grid
var int: NWALLS = sum([walls_grid[wx, wy] | wx in WIDTH, wy in HEIGHT]);
var int: NWALLED = sum([1 | x in WIDTH, y in HEIGHT where 
                                  sum([walls_grid[wx, wy] | wx in WIDTH, wy in HEIGHT where wx == x /\ wy > y]) mod 2 == 1
                         ]);

% cells of walls_grid are either 0 (no wall) or 1 (wall)
constraint  
  forall (x in WIDTH) (
    forall (y in HEIGHT) (
      walls_grid[x,y] == 0 \/ walls_grid[x,y] == 1
  )
);
  

% each of the D points must be surrounded by V non-walled points, with V being the number in the point of interest
constraint
  forall (x in WIDTH, y in HEIGHT) (
        if grid[x,y] != 0 then
          forall (wx in WIDTH, wy in HEIGHT where walls_grid[wx, wy] == 1) (
            abs(wx - x) + abs(wy - y) > grid[x,y]
          )
        endif
  );


% walls must be all adjacent (every wall has another wall near it, vertically/horizontally/diagonally)
constraint
  forall (wx in WIDTH, wy in HEIGHT where walls_grid[wx, wy] == 1) (
    walls_grid[wx - 1, wy - 1] == 1 \/
    walls_grid[wx - 1, wy]     == 1 \/
    walls_grid[wx - 1, wy + 1] == 1 \/
    
    walls_grid[wx, wy - 1] == 1     \/
    walls_grid[wx, wy + 1] == 1     \/
    
    walls_grid[wx + 1, wy - 1] == 1 \/
    walls_grid[wx + 1, wy]     == 1 \/
    walls_grid[wx + 1, wy + 1] == 1
  );


% each of the D points must be delimited (i.e., an odd number of walls are on the same horizontal coordinate)
constraint
  forall(x in WIDTH) (
    forall(y in HEIGHT) (
      if grid[x,y] != 0 then
        % the amount of walls on the same horizontal coordinate and with a higher vertical coordinate (i.e. the walls "encountered" by the ray starting on the point)
        sum([walls_grid[wx, wy] | wx in WIDTH, wy in HEIGHT where wx == x /\ wy > y]) mod 2 == 1
      endif
    )
  );


% NWALLED has priority; we weigh it the maximum possible value of NWALLS to ensure this
solve minimize R*C*NWALLED + NWALLS;

output ["\(NWALLS)\n"] ++
       ["\(wx) \(wy)\n" | wx in WIDTH, wy in HEIGHT where fix(walls_grid[wx, wy]) == 1]
 