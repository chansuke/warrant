----------------------------- MODULE Discharge -----------------------------
(* `verify::discharge`: workers share one locked iterator over the         *)
(* obligations and each writes its result into the slot of the index it   *)
(* took. Checked: no obligation is solved twice, every slot ends up with   *)
(* its own obligation's result (results keep the obligations' order), and  *)
(* all workers finish, so the final `expect` never panics. Without Locked, *)
(* taking reads and advances the iterator in two steps, and AtMostOnce     *)
(* fails: the lock is what makes the rest hold.                            *)
EXTENDS Naturals

CONSTANTS N, Workers, Locked

None == 0
Solve(i) == i   \* Stands for "the result of obligation i"; any injection works.

VARIABLES next, held, pc, results, solved, peek
vars == <<next, held, pc, results, solved, peek>>

Init ==
  /\ next = 1
  /\ held = [w \in Workers |-> None]
  /\ pc = [w \in Workers |-> "take"]
  /\ results = [i \in 1..N |-> None]
  /\ solved = [i \in 1..N |-> 0]
  /\ peek = [w \in Workers |-> None]

(* `queue.lock().unwrap().next()`: atomic under the mutex.                 *)
TakeFrom(w, i) ==
  IF i <= N
    THEN /\ held' = [held EXCEPT ![w] = i]
         /\ next' = i + 1
         /\ pc' = [pc EXCEPT ![w] = "solve"]
    ELSE /\ pc' = [pc EXCEPT ![w] = "done"]
         /\ UNCHANGED <<held, next>>

Take(w) ==
  /\ pc[w] = "take"
  /\ IF Locked
       THEN TakeFrom(w, next) /\ UNCHANGED peek
       ELSE /\ peek' = [peek EXCEPT ![w] = next]
            /\ pc' = [pc EXCEPT ![w] = "advance"]
            /\ UNCHANGED <<held, next>>
  /\ UNCHANGED <<results, solved>>

(* Only without Locked: the second half of an unlocked take.               *)
Advance(w) ==
  /\ pc[w] = "advance"
  /\ TakeFrom(w, peek[w])
  /\ UNCHANGED <<results, solved, peek>>

(* Solving runs outside the lock; storing the result takes the other lock. *)
Store(w) ==
  /\ pc[w] = "solve"
  /\ results' = [results EXCEPT ![held[w]] = Solve(held[w])]
  /\ solved' = [solved EXCEPT ![held[w]] = @ + 1]
  /\ held' = [held EXCEPT ![w] = None]
  /\ pc' = [pc EXCEPT ![w] = "take"]
  /\ UNCHANGED <<next, peek>>

AllDone == \A w \in Workers : pc[w] = "done"
Next == (\E w \in Workers : Take(w) \/ Advance(w) \/ Store(w)) \/ (AllDone /\ UNCHANGED vars)
Spec == Init /\ [][Next]_vars /\ \A w \in Workers : WF_vars(Take(w) \/ Advance(w) \/ Store(w))

AtMostOnce == \A i \in 1..N : solved[i] <= 1
InOrder == \A i \in 1..N : results[i] \in {None, Solve(i)}
Complete == AllDone => \A i \in 1..N : results[i] = Solve(i)
Finishes == <>AllDone
=============================================================================
