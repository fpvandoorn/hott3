/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
-/
import algebra.ring
open algebra pointed is_trunc

namespace algebra
structure Semigroup :=
(carrier : Type _) (struct : semigroup carrier)

attribute Semigroup.carrier [coercion]
attribute Semigroup.struct [instance]

structure CommSemigroup :=
(carrier : Type _) (struct : comm_semigroup carrier)

attribute CommSemigroup.carrier [coercion]
attribute CommSemigroup.struct [instance]

structure Monoid :=
(carrier : Type _) (struct : monoid carrier)

attribute Monoid.carrier [coercion]
attribute Monoid.struct [instance]

structure CommMonoid :=
(carrier : Type _) (struct : comm_monoid carrier)

attribute CommMonoid.carrier [coercion]
attribute CommMonoid.struct [instance]

structure Group :=
(carrier : Type _) (struct' : group carrier)

attribute Group.struct' [instance]

section
local attribute Group.carrier [coercion]
@[hott] def pSet_of_Group [reducible] [coercion] (G : Group) : Set* :=
ptrunctype.mk (Group.carrier G) !semigroup.is_set_carrier 1
end

@[hott] def Group.struct [instance] [priority 2000] (G : Group) : group G :=
Group.struct' G

attribute algebra._trans_of_pSet_of_Group
attribute algebra._trans_of_pSet_of_Group_1 algebra._trans_of_pSet_of_Group_2

@[hott] def pType_of_Group [reducible] (G : Group) : Type* :=
G
@[hott] def Set_of_Group [reducible] (G : Group) : Set :=
G

@[hott] def AddGroup : Type _ := Group

@[hott] def pSet_of_AddGroup [reducible] [coercion] (G : AddGroup) : Set* :=
pSet_of_Group G

@[hott] def AddGroup.mk [reducible] (G : Type _) (H : add_group G) : AddGroup :=
Group.mk G H

@[hott] def AddGroup.struct [reducible] [instance] [priority 2000] (G : AddGroup) : add_group G :=
Group.struct G

attribute algebra._trans_of_pSet_of_AddGroup
attribute algebra._trans_of_pSet_of_AddGroup_1 algebra._trans_of_pSet_of_AddGroup_2

@[hott] def pType_of_AddGroup [reducible] : AddGroup → Type* :=
algebra._trans_of_pSet_of_AddGroup_1
@[hott] def Set_of_AddGroup [reducible] : AddGroup → Set :=
algebra._trans_of_pSet_of_AddGroup_2

structure AbGroup :=
(carrier : Type _) (struct' : ab_group carrier)

attribute AbGroup.struct' [instance]

section
local attribute AbGroup.carrier [coercion]
@[hott] def Group_of_AbGroup [coercion] (G : AbGroup) : Group :=
Group.mk G _
end

@[hott] def AbGroup.struct [instance] [priority 2000] (G : AbGroup) : ab_group G :=
AbGroup.struct' G

attribute algebra._trans_of_Group_of_AbGroup_1
          algebra._trans_of_Group_of_AbGroup
          algebra._trans_of_Group_of_AbGroup_3
attribute algebra._trans_of_Group_of_AbGroup_2

@[hott] def AddAbGroup : Type _ := AbGroup

@[hott] def AddGroup_of_AddAbGroup [coercion] (G : AddAbGroup) : AddGroup :=
Group_of_AbGroup G

@[hott] def AddAbGroup.struct [reducible] [instance] [priority 2000] (G : AddAbGroup) :
  add_ab_group G :=
AbGroup.struct G

@[hott] def AddAbGroup.mk [reducible] (G : Type _) (H : add_ab_group G) :
  AddAbGroup :=
AbGroup.mk G H

attribute algebra._trans_of_AddGroup_of_AddAbGroup_1
          algebra._trans_of_AddGroup_of_AddAbGroup
          algebra._trans_of_AddGroup_of_AddAbGroup_3
attribute algebra._trans_of_AddGroup_of_AddAbGroup_2

-- structure AddSemigroup :=
-- (carrier : Type _) (struct : add_semigroup carrier)

-- attribute AddSemigroup.carrier [coercion]
-- attribute AddSemigroup.struct [instance]

-- structure AddCommSemigroup :=
-- (carrier : Type _) (struct : add_comm_semigroup carrier)

-- attribute AddCommSemigroup.carrier [coercion]
-- attribute AddCommSemigroup.struct [instance]

-- structure AddMonoid :=
-- (carrier : Type _) (struct : add_monoid carrier)

-- attribute AddMonoid.carrier [coercion]
-- attribute AddMonoid.struct [instance]

-- structure AddCommMonoid :=
-- (carrier : Type _) (struct : add_comm_monoid carrier)

-- attribute AddCommMonoid.carrier [coercion]
-- attribute AddCommMonoid.struct [instance]

-- structure AddGroup :=
-- (carrier : Type _) (struct : add_group carrier)

-- attribute AddGroup.carrier [coercion]
-- attribute AddGroup.struct [instance]

-- structure AddAbGroup :=
-- (carrier : Type _) (struct : add_ab_group carrier)

-- attribute AddAbGroup.carrier [coercion]
-- attribute AddAbGroup.struct [instance]


-- some bundled infinity-structures
structure InfGroup :=
(carrier : Type _) (struct' : inf_group carrier)

attribute InfGroup.struct' [instance]

section
  local attribute InfGroup.carrier [coercion]
  @[hott] def pType_of_InfGroup [reducible] [coercion] (G : InfGroup) : Type* :=
  pType.mk G 1
end

attribute algebra._trans_of_pType_of_InfGroup

@[hott] def InfGroup.struct [instance] [priority 2000] (G : InfGroup) : inf_group G :=
InfGroup.struct' G

@[hott] def AddInfGroup : Type _ := InfGroup

@[hott] def pType_of_AddInfGroup [reducible] [coercion] (G : AddInfGroup) : Type* :=
pType_of_InfGroup G

@[hott] def AddInfGroup.mk [reducible] (G : Type _) (H : add_inf_group G) :
  AddInfGroup :=
InfGroup.mk G H

@[hott] def AddInfGroup.struct [reducible] (G : AddInfGroup) : add_inf_group G :=
InfGroup.struct G

attribute algebra._trans_of_pType_of_AddInfGroup

structure AbInfGroup :=
(carrier : Type _) (struct' : ab_inf_group carrier)

attribute AbInfGroup.struct' [instance]

section
local attribute AbInfGroup.carrier [coercion]
@[hott] def InfGroup_of_AbInfGroup [coercion] (G : AbInfGroup) : InfGroup :=
InfGroup.mk G _
end

@[hott] def AbInfGroup.struct [instance] [priority 2000] (G : AbInfGroup) : ab_inf_group G :=
AbInfGroup.struct' G

attribute algebra._trans_of_InfGroup_of_AbInfGroup_1
attribute algebra._trans_of_InfGroup_of_AbInfGroup

@[hott] def AddAbInfGroup : Type _ := AbInfGroup

@[hott] def AddInfGroup_of_AddAbInfGroup [coercion] (G : AddAbInfGroup) : AddInfGroup :=
InfGroup_of_AbInfGroup G

@[hott] def AddAbInfGroup.struct [reducible] [instance] [priority 2000] (G : AddAbInfGroup) :
  add_ab_inf_group G :=
AbInfGroup.struct G

@[hott] def AddAbInfGroup.mk [reducible] (G : Type _) (H : add_ab_inf_group G) :
  AddAbInfGroup :=
AbInfGroup.mk G H

attribute algebra._trans_of_AddInfGroup_of_AddAbInfGroup_1
attribute algebra._trans_of_AddInfGroup_of_AddAbInfGroup

@[hott] def InfGroup_of_Group (G : Group) : InfGroup :=
InfGroup.mk G _

@[hott] def AddInfGroup_of_AddGroup (G : AddGroup) : AddInfGroup :=
AddInfGroup.mk G _

@[hott] def AbInfGroup_of_AbGroup (G : AbGroup) : AbInfGroup :=
AbInfGroup.mk G _

@[hott] def AddAbInfGroup_of_AddAbGroup (G : AddAbGroup) : AddAbInfGroup :=
AddAbInfGroup.mk G _

/- rings -/
structure Ring :=
(carrier : Type _) (struct : ring carrier)

attribute Ring.carrier [coercion]
attribute Ring.struct [instance]

end algebra
