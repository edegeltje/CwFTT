import CwFTT.PartialMap.Classifier

import Mathlib.CategoryTheory.Preadditive.Injective.Basic

universe v u
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C]

instance [HasPullbacks C] {Y : C} (𝒞 : PartialMap.Classifier Y) : Injective (𝒞.obj) where
  factors {U X} f m _ := by
    use 𝒞.χ (pullback.snd f (𝒞.η)) (pullback.fst f (𝒞.η) ≫ m)
    have := 𝒞.isPullback (pullback.snd f (𝒞.η)) (pullback.fst f (𝒞.η))
    have := 𝒞.isPullback (pullback.snd f (𝒞.η)) (pullback.fst f 𝒞.η ≫ m)
    trans 𝒞.χ (pullback.snd f (𝒞.η)) (pullback.fst f (𝒞.η))
    · apply 𝒞.uniq
      exact this.shift_mono_top
    · symm
      apply 𝒞.uniq
      exact .of_hasPullback _ _


end CategoryTheory
