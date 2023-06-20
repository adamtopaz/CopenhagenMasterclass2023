/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ExtrDisc.Basic

/-!
# The category of extremally disconnected spaces is precoherent

This file contains a proof that the category of extremally disconnected
spaces is precoherent. Precoherence is the claim that "effective epis pull back"
and is the condition we'll use to define a *coverage* on `ExtrDisc`, which
is a collection of covering presieves satisfying a pullback condition.

## TODO

Supply the proof!

-/
universe u

open CategoryTheory

namespace ExtrDisc

instance : Precoherent ExtrDisc.{u} := sorry

end ExtrDisc
