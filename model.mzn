include "globals.mzn";

int: R; % number of rows
int: C; % number of columns
set of int: HEIGHT = 1..R;
set of int: WIDTH = 1..C;
array [WIDTH,HEIGHT] of int: grid;


enum Cell = {Empty, Wall};
% encode each Wall point as R * (wx - 1) + wy (i.e. R is the "base" of this encoding)
array [1..C*R] of var Cell: walls;

% TODO: convert grid to single one-dimensional array

% TODO: define a predicate for "walled cell" given coordinates and grid
var int: NWALLS = card({j | j in 1..C*R where walls[j] == Wall});
var int: NWALLED = sum([1 | x in WIDTH, y in HEIGHT where 
                                  walled(x,y)
                         ]);
    
% the amount of walls on the same horizontal/vertical coordinate and with a higher vertical/horizontal coordinate (i.e. the walls "encountered" by the ray starting on the point)
predicate walled(int: x, int: y) = 
      card({wy | wy in HEIGHT where wy > y /\ walls[R * (x - 1) + wy] == Wall}) mod 2 == 1 /\
      card({wx | wx in WIDTH where wx > x /\ walls[R * (wx - 1) + y] == Wall}) mod 2 == 1;

% each of the D points must be surrounded by V non-walled points, with V being the number in the point of interest
constraint
  forall (x in WIDTH, y in HEIGHT where grid[x,y] != 0) (
    forall (j in 1..C*R) (
      let {
        var int: wx = (j div R) + 1;
        var int: wy = if j mod R != 0 then j mod R else R endif;
      } in
      (abs(wx - x) + abs(wy - y) <= grid[x,y]) ->
      walls[j] == Empty
    )
  );


constraint
%     decreasing(walls_array) /\
    forall (i in 1..C*R where walls[i] == Wall) (
        let {
         % succ is the first index larger than i with where there is a Wall
          var set of int: successors = {j | j in 1..C*R where j > i /\ walls[j] == Wall};
          
          var int: succ = if i <= C*R /\ card(successors) > 0 then
                           min(successors)
                         else 
                           min({j | j in 1..C*R where walls[j] == Wall})
                         endif;
                         
          var int: wx = (i div R) + 1;
          var int: wy = if i mod R != 0 then i mod R else R endif;
          
          var int: sx = (succ div R) + 1;
          var int: sy = if succ mod R != 0 then succ mod R else R endif
        } in
        
%         succ == R * (wx - 1) + (wy + 1) \/
%         succ == R * (wx - 1) + (wy - 1) \/
        
%         succ == R * (wx - 2) + (wy - 1) \/
%         succ == R * (wx - 2) + (wy)     \/
%         succ == R * (wx - 2) + (wy + 1) \/
        
%         succ == R * (wx) + (wy - 1) \/
%         succ == R * (wx) + (wy)     \/
%         succ == R * (wx) + (wy + 1)          
          abs(wx - sx) <= 1 /\
          abs(wy - sy) <= 1 /\
          not (wx == sx /\ wy == sy)
    );


% each of the D points must be delimited (i.e., an odd number of walls are on the same horizontal coordinate)
constraint
  forall(x in WIDTH, y in HEIGHT where grid[x,y] != 0) (
      walled(x,y)
  );


% NWALLED has priority; we weigh it with the maximum possible value of NWALLS to ensure this
solve minimize R*C*NWALLED + NWALLS;
% solve satisfy;

output ["\(NWALLS)\n"] ++
       ["\(wx) \(wy)\n" | wx in WIDTH, wy in HEIGHT where fix(walls[R * (wx - 1) + wy]) == Wall]
 