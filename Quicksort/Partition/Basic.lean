import Quicksort.Partition.Hoare.Basic
import Quicksort.Partition.Lomuto.Basic

-- instance instInhabitedSchemeOfOrd : Inhabited (Partition.Scheme α) := ⟨@Partition.lomuto (α := α)⟩
instance instInhabitedSchemeOfOrd' : Inhabited (Partition.Scheme α) := ⟨@Partition.hoare (α := α)⟩
