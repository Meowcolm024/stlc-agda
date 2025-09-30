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

-- anti-rename
import stlc.strengthen

-- program equivalence
import stlc.equiv

-- substitution lemma (adapted from PLFA)
import stlc.subst
