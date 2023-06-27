/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.Profinite.Basic
import Profinite.Epi
/-!

# The category of profinite spaces is precoherent

-/
namespace Profinite

open CategoryTheory

universe u

instance : Precoherent Profinite.{u} := by
  constructor
  intro B₁ B₂ f α _ X₁ π₁ h₁
  refine ⟨α, inferInstance, fun a => pullback f (π₁ a), fun a => pullback.fst _ _, ?_,
    id, fun a => pullback.snd _ _, ?_⟩
  · have := (effectiveEpiFamily_tfae _ π₁).out 0 2 ; rw [this] at h₁ ; clear this
    have := (effectiveEpiFamily_tfae _ (fun a => pullback.fst f (π₁ a))).out 0 2
    rw [this] ; clear this
    intro b₂
    obtain ⟨a,x,h⟩ := h₁ (f b₂)
    refine ⟨a, ⟨⟨b₂, x⟩, h.symm⟩, rfl⟩
  · intro a
    dsimp
    ext ⟨⟨_,_⟩,h⟩
    exact h.symm

end Profinite
