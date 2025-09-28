module stlc where

-- stlc with booleans
-- terms, types, typing and smallstep semantic
import stlc.base

-- basic lemmas and proofs
-- progress, preservation ect
import stlc.prop

-- environment base bigstep semantic
import stlc.bigstep

-- (weak) normalization
import stlc.norm

-- semantic type safety
import stlc.safety

-- anti-rename
import stlc.strengthen

-- substitution lemma
import stlc.subst
