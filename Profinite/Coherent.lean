/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.Profinite.Basic
/-!

# The category of profinite spaces is precoherent

# TODO

Prove the theorem that the category of profinite spaces
is precoherent.

-/
namespace Profinite

open CategoryTheory

universe u

instance : Precoherent Profinite.{u} := sorry

end Profinite