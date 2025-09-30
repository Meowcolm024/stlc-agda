module stlc where

-- stlc with booleans
-- terms, types, typing and reudction
import stlc.base

-- basic lemmas and proofs
-- progress, preservation etc
import stlc.prop

-- environment-base bigstep semantic (adapted from PLFA)
import stlc.bigstep

-- (weak) normalization
import stlc.norm

-- semantic type soundness
import stlc.safety

-- program equivalence
import stlc.equiv

-- anti-rename
import stlc.strengthen

-- substitution lemma (adapted from PLFA)
import stlc.subst
