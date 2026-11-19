---------------------------- MODULE ProofCache ----------------------------
(* The proof cache of src/cache.rs, run by several `warrant check`         *)
(* processes at once. Each cache file holds one entry: the script it was   *)
(* proved for and the outcome. Two scripts may hash to the same file.      *)
(*                                                                         *)
(* A write is not atomic: it puts the script field, then the status field. *)
(* A read takes whatever the file holds at that moment. With Atomic, a     *)
(* writer fills a private temp file and renames it over the cache file, as *)
(* `Cache::put` does; without it, the writer writes the cache file in      *)
(* place. Sound must hold with Atomic and fails without it.                *)
EXTENDS Naturals

CONSTANTS Procs, Scripts, Files, Hash, Result, Atomic

None == "none"
Empty == [script |-> None, status |-> None]
Outcomes == {Result[s] : s \in Scripts}

VARIABLES dir, tmp, pc, job, seen
vars == <<dir, tmp, pc, job, seen>>

TypeOK ==
  /\ dir \in [Files -> [script : Scripts \cup {None}, status : Outcomes \cup {None}]]
  /\ tmp \in [Procs -> [script : Scripts \cup {None}, status : Outcomes \cup {None}]]
  /\ pc \in [Procs -> {"get", "w0", "w1", "w2", "rename"}]
  /\ job \in [Procs -> Scripts]

Init ==
  /\ dir = [f \in Files |-> Empty]
  /\ tmp = [p \in Procs |-> Empty]
  /\ pc = [p \in Procs |-> "get"]
  /\ job \in [Procs -> Scripts]
  /\ seen = [p \in Procs |-> [script |-> None, got |-> None]]

(* `Cache::get`: a hit only when the stored script is this script.         *)
Get(p) ==
  LET e == dir[Hash[job[p]]]
      hit == e.script = job[p] /\ e.status # None
  IN /\ pc[p] = "get"
     /\ seen' = [seen EXCEPT ![p] = [script |-> job[p], got |-> IF hit THEN e.status ELSE "miss"]]
     /\ IF hit
          THEN /\ pc' = [pc EXCEPT ![p] = "get"]
               /\ job' \in [Procs -> Scripts] /\ \A q \in Procs \ {p} : job'[q] = job[q]
          ELSE /\ pc' = [pc EXCEPT ![p] = "w0"]
               /\ UNCHANGED job
     /\ UNCHANGED <<dir, tmp>>

(* The file being written: the temp file, or the cache file in place.      *)
Target(p) == IF Atomic THEN tmp[p] ELSE dir[Hash[job[p]]]
Put(p, e) ==
  IF Atomic THEN /\ tmp' = [tmp EXCEPT ![p] = e] /\ UNCHANGED dir
            ELSE /\ dir' = [dir EXCEPT ![Hash[job[p]]] = e] /\ UNCHANGED tmp

Truncate(p) ==
  /\ pc[p] = "w0" /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ Put(p, Empty)
  /\ UNCHANGED <<job, seen>>

WriteScript(p) ==
  /\ pc[p] = "w1" /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ Put(p, [Target(p) EXCEPT !.script = job[p]])
  /\ UNCHANGED <<job, seen>>

WriteStatus(p) ==
  /\ pc[p] = "w2" /\ pc' = [pc EXCEPT ![p] = IF Atomic THEN "rename" ELSE "get"]
  /\ Put(p, [Target(p) EXCEPT !.status = Result[job[p]]])
  /\ UNCHANGED <<job, seen>>

Rename(p) ==
  /\ pc[p] = "rename" /\ pc' = [pc EXCEPT ![p] = "get"]
  /\ dir' = [dir EXCEPT ![Hash[job[p]]] = tmp[p]]
  /\ tmp' = [tmp EXCEPT ![p] = Empty]
  /\ UNCHANGED <<job, seen>>

Next == \E p \in Procs :
  Get(p) \/ Truncate(p) \/ WriteScript(p) \/ WriteStatus(p) \/ Rename(p)

Spec == Init /\ [][Next]_vars

(* What p's last get returned, for which script. A hit is always that      *)
(* script's own outcome: never a colliding script's, never half of one.    *)
Sound == \A p \in Procs :
  seen[p].script # None => seen[p].got \in {"miss", Result[seen[p].script]}

(* Readers only ever see an empty file or a whole, consistent entry.       *)
Whole == Atomic => \A f \in Files :
  dir[f] = Empty \/ (dir[f].script # None /\ dir[f].status = Result[dir[f].script])
=============================================================================
