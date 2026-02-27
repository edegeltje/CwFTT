import CwFTT.Classifier.And

universe v u
namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open MonoidalCategory

structure LTT [CartesianMonoidalCategory C] (𝒞 : Classifier C) where
  locally : 𝒞.Ω ⟶ 𝒞.Ω
  locally_true : 𝒞.truth ≫ locally = 𝒞.truth
  locally_locally : locally ≫ locally = locally
  locally_and : 𝒞.and ≫ locally = (locally ⊗ₘ locally) ≫ 𝒞.and

attribute [reassoc] LTT.locally_true LTT.locally_locally LTT.locally_and

end CategoryTheory
