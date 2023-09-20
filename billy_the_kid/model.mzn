include "globals.mzn";
include "alldifferent.mzn";

array[_] of int: town1;
array[_] of int: connected1;
array[_] of int: connected2;
array[_] of int: townsintravel1;

array[1..length(connected1)] of tuple(int,int): connections = [(connected1[i],connected2[i]) | i in 1..length(connected1)];

array[1..length(town1)] of var 0..1: selected;
array[1..townsintravel1[1]] of var 1..max(town1): path; %[2,3,4] 

constraint
  all_different(path) /\
  forall(j in 2..townsintravel1[1])(
      exists(c in connections)
        (
          (path[j] == c.1 /\ path[j - 1] == c.2) \/
          (path[j] == c.2 /\ path[j - 1] == c.1)
        )
  );

constraint exists(t in path)(selected[t] == 1);
   
solve minimize sum(selected);

