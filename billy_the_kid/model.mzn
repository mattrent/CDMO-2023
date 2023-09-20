include "globals.mzn";
include "alldifferent.mzn";

array[_] of int: town1;
array[_] of int: connected1;
array[_] of int: connected2;
array[_] of int: townsintravel1;

% set of int: NSEQ = 1..pow(length(town1), townsintravel1[1]);

array[1..length(connected1)] of tuple(int,int): connections = [(connected1[i],connected2[i]) | i in 1..length(connected1)];
set of int: NSEQ = 1..product([length(town1) - x | x in 0..(townsintravel1[1]-1)]);


array[1..length(town1)] of var 0..1: selected;
array[NSEQ, 1..townsintravel1[1]] of var 0..length(town1): seqs; %[2,3,4] 

predicate all_paths_different(array[NSEQ, 1..townsintravel1[1]] of var 1..length(town1): seqs) = 
  forall(i,j in NSEQ where i!=j) (
    let {
       array[1..townsintravel1[1]] of var int: path1 = row(seqs, i);
       array[1..townsintravel1[1]] of var int: path2 = row(seqs, j);
    } in
    (path(path1) /\ path(path2)) -> array2set(path1) != array2set(path2)
  );

% every sequence is either a path or all zeros; if a sequence is all zeros, then all the following sequences are also made of zeros 
predicate all_paths_or_zero(array[NSEQ, 1..townsintravel1[1]] of var 1..length(town1): seqs) =
  forall(i in NSEQ) (
    path(row(seqs, i)) \/
    (sum(row(seqs, i)) == 0 /\
      forall(j in NSEQ where j > i)
        (sum(row(seqs, j)) == 0)
    )
  );

  

predicate path(array[1..townsintravel1[1]] of var 1..length(town1): seq) =
    all_different(seq) /\
    forall(j in 2..townsintravel1[1])(
        exists(c in connections)
          (
            (seq[j] == c.1 /\ seq[j - 1] == c.2) \/
            (seq[j] == c.2 /\ seq[j - 1] == c.1)
          )
    );


constraint all_paths_different(seqs);
constraint all_paths_or_zero(seqs);

constraint   
  forall(i in NSEQ where path(row(seqs, i))) (
    let {
      array[1..townsintravel1[1]] of var int: path = row(seqs, i);
    } in
    exists(t in path)(selected[t] == 1)
  );
 
% Costringe a generare il numero massimo possible di path -> problema, considera importante l'ordine, perché è un array, e quindi lo spazio delle soluzioni esplode
% solve minimize ((length(town1) + 1) * -1 * sum([1 | i in NSEQ where path(row(paths, i))])) + sum(selected);
solve maximize ((length(town1) + 1) * card({i | i in NSEQ where path(row(seqs, i))})) - sum(selected);

