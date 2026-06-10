import Quicksort.Partition.Hoare.Basic
import Quicksort.Partition.Lomuto.Basic

-- instance instInhabitedSchemeOfOrd [BLt α] : Inhabited (Partition.Scheme α) := ⟨Partition.lomuto⟩
instance instInhabitedSchemeOfOrd' [BLt α] : Inhabited (Partition.Scheme α) := ⟨Partition.hoare⟩
