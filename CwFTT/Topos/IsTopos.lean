import CwFTT.Topos.ToposData

universe v u

namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

variable (C) in
def IsTopos := Nonempty (ToposData C)




end CategoryTheory
