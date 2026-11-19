--------------------------- MODULE MCProofCache ---------------------------
(* s1 and s2 collide in f1 and have different outcomes.                    *)
EXTENDS ProofCache

MCHash == [s \in {"s1", "s2", "s3"} |-> IF s = "s3" THEN "f2" ELSE "f1"]
MCResult == [s \in {"s1", "s2", "s3"} |-> IF s = "s2" THEN "failed" ELSE "proved"]
=============================================================================
