include "globals.mzn";
include "alldifferent.mzn";

array[_] of int: town1;
array[_] of int: connected1;
array[_] of int: connected2;
array[_] of int: townsintravel1;

array[1..length(connected1)] of tuple(int,int): connections = [(connected1[i],connected2[i]) | i in 1..length(connected1)];


array[1..length(town1)] of var 0..1: selected;

% is set of nodes "end" reachable from node "start" in every path of "length" steps?
predicate reach(var int: start, var set of int: end, int: length, var set of int: visited, array[1..length(connected1)] of tuple(int,int): connections) =
  % was "end" reached in this path?
  if (end intersect visited != {}) \/ (start in end) then
    true
  else
    % 0 steps left, failed
    if length == 0 then
      false
    else
      let {
        % nodes reachable from "start" in one step (connections are bi-directional, so we consider both from and to)
        var set of int: from_start = {c.2 | c in connections where start == c.1}; 
        var set of int: to_start   = {c.1 | c in connections where start == c.2};
        var set of int: connected = from_start union to_start;
        % connected nodes that weren't visited (avoid loops)
        var set of int: connected_not_visited = connected diff visited;
      } in
      % is "end" reachable in length-1 steps from all connected nodes?
      forall(t in connected_not_visited)(
        reach(t, end, length - 1, visited union {start}, connections)
      )
    endif
  endif;

%TODO: we want all nodes to be reachable from "selected"
constraint
  forall(i in 1..length(town1))(
      reach(i, {j | j in 1..length(town1) where selected[j] == 1}, townsintravel1[1] - 1, {}, connections)
  );

solve minimize sum(selected);

