import Mathlib
import Mathlib.Topology.Separation
import M2.alpha
import M2.K_stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (p:X) (F:preSheaf Ab (of X))

#check Kstalk X p ((AlphaUpStar X).obj F)

#check Functor.comp (AlphaUpStar X) (KstalkFunctor X p)
#check @stalkFunctor Ab _ _ (of X) p

#check Functor.comp (AlphaUpStar X) (KstalkFunctor X p) ≅ @stalkFunctor Ab _ _ (of X) p
