/-!
How to talk about internal language in lean?

-/
import Mathlib.CategoryTheory.Basic

universe v u w


opaque IsTopos (E : Type u) : Type


class InterpretTypeInToposAs {E : Type u} [Category.{v} E] (hE : IsTopos E) (X : Sort v) where
  asObj : E


-- instance : InterpretTypeInToposAs {E : Type u} (hE : IsTopos E) := sorry

/-- this should give the subobject classifier -/

instance InterpretTypeInToposAs.prop {E : Type u} (hE : IsTopos E) := sorry

class InterpretElemInToposAs {E : Type u} [Category.{v} E] (hE : IsTopos E) {X : Sort v} (x : X) extends
    InterpretTypeInToposAs hE X where
  asElem : asObj → asObj


-- instance (E : Type u) (hE : IsTopos E) (p q : Prop) : InterpretInToposAs hE (p ∧ q)



/-

-- how to interpret a term `x : X` in a topos


instance Interpret

-/
