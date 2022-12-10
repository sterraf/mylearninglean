import set_theory.cardinal.ordinal

universe u 

open set

namespace cardinal

open_locale cardinal

set_option pp.all true
variables (i k : ordinal.{u})

#check lift.{u+1} (# (↥(Iio.{u+1} i))) -- `cardinal.{u+1}`
#check lift.{u+1} (# (quotient.out.{u+2} i).α) -- `cardinal.{u+1}`
#check lift.{u+1} (# (↥(Iio.{u+1} i))) = lift.{u+1} (# (quotient.out.{u+2} i).α) -- type mismatch at application

/-
term
  cardinal.lift.{u+1 u} (cardinal.mk.{u} (@quotient.out.{u+2} Well_order.{u} ordinal.is_equivalent.{u} i).α)
has type
  cardinal.{u+1}
but is expected to have type
  cardinal.{u+1}
-/

#check lift.{u+1} (# (↥(Iio.{u+1} i)))
 = (lift.{u+1} (# (quotient.out.{u+2} i).α) : cardinal.{u+1})


end cardinal