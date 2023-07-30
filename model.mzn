include "globals.mzn";

int: R; % number of rows
int: C; % number of columns
set of int: HEIGHT = 1..R;
set of int: WIDTH = 1..C;
array [WIDTH,HEIGHT] of int: grid;


enum Cell = {Empty, Wall};
array [WIDTH, HEIGHT] of var Cell: walls_grid; % computed grid of 0 (free cells) and 1 (walls)

% TODO: convert grid to single one-dimensional array

% TODO: define a predicate for "walled cell" given coordinates and grid
var int: NWALLS = card({(R+1) * wx + wy | wx in WIDTH, wy in HEIGHT where walls_grid[wx, wy] == Wall});
% var int: NWALLED = sum([1 | x in WIDTH, y in HEIGHT where 
%                                   sum([1 | wx in WIDTH, wy in HEIGHT where 
%                                           wx == x 
%                                           /\ wy > y 
%                                           /\ walls_grid[wx, wy] == Wall]) mod 2 == 1
%                          ]);
    

% each of the D points must be surrounded by V non-walled points, with V being the number in the point of interest
% TODO: this might not be working
constraint
  forall (x in WIDTH, y in HEIGHT where grid[x,y] != 0) (
    forall (wx in WIDTH, wy in HEIGHT where walls_grid[wx, wy] == Wall) (
      abs(wx - x) + abs(wy - y) > grid[x,y]
    )
  );


constraint
%TODO: just check the first valid index where a Wall is found in the 1-dimensional array
    let {
       % encode each Wall point as (R + 1) * wx + wy (i.e. R+1 is the "base" of this encoding)
       array[1..C*R] of var int: walls_array = [
         if walls_grid[wx, wy] == Wall then (R + 1) * wx + wy 
         else -1 endif
        | wx in WIDTH, wy in HEIGHT
       ];
    } in
%     decreasing(walls_array) /\
    forall (i in 1..C*R where walls_array[i] != -1) (
        let {
          var int: wx = walls_array[i] div (R + 1);
          var int: wy = walls_array[i] mod (R + 1);

         % succ is the first index larger than i with where there is a Wall
          var set of int: successors = {j | j in 1..C*R where j > i /\ walls_array[j] != -1};
          
          var int: succ = if i <= C*R /\ card(successors) > 0 then
                           min(successors)
                         else 1 endif;
        } in
      
        walls_array[succ] == (R + 1) * (wx) + (wy - 1) \/
        walls_array[succ] == (R + 1) * (wx) + (wy + 1) \/
        
        walls_array[succ] == (R + 1) * (wx - 1) + (wy - 1) \/
        walls_array[succ] == (R + 1) * (wx - 1) + (wy)     \/
        walls_array[succ] == (R + 1) * (wx - 1) + (wy + 1) \/
        
        walls_array[succ] == (R + 1) * (wx + 1) + (wy - 1) \/
        walls_array[succ] == (R + 1) * (wx + 1) + (wy)     \/
        walls_array[succ] == (R + 1) * (wx + 1) + (wy + 1)          
    );


% each of the D points must be delimited (i.e., an odd number of walls are on the same horizontal coordinate)
constraint
  forall(x in WIDTH, y in HEIGHT where grid[x,y] != 0) (
      % the amount of walls on the same horizontal coordinate and with a higher vertical coordinate (i.e. the walls "encountered" by the ray starting on the point)
      card({wy | wy in HEIGHT where wy > y /\ walls_grid[x, wy] == Wall}) mod 2 == 1
  );


% NWALLED has priority; we weigh it the maximum possible value of NWALLS to ensure this
% solve minimize R*C*NWALLED + NWALLS;
solve satisfy;

output ["\(NWALLS)\n"] ++
       ["\(wx) \(wy)\n" | wx in WIDTH, wy in HEIGHT where fix(walls_grid[wx, wy]) == Wall]
 