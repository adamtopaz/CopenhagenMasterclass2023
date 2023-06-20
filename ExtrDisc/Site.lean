/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ExtrDisc.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi
import FindWithGpt

/-!
# The coverage on extremally disconnected spaces

This file constructs a coverage on the category of extremally disconnected
spaces. This coverage is compatible with the coherent coverage on `CompHaus`.

## TODO

Supply the proof!

-/
universe u

open CategoryTheory

namespace ExtrDisc

def coverage : Coverage ExtrDisc.{u} where
  covering X := { S | S.functorPushforward toCompHaus ∈ coherentCoverage _ X.compHaus }
  pullback := sorry

def grothendieckTopology : GrothendieckTopology ExtrDisc.{u} := 
  Coverage.toGrothendieck _ coverage

end ExtrDisc
