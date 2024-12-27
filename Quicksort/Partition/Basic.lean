import Quicksort.Partition.Hoare.Basic
import Quicksort.Partition.Lomuto.Basic

instance instInhabitedSchemeOfOrd [Ord α] : Inhabited (Partition.Scheme α) := ⟨Partition.lomuto⟩
instance instInhabitedSchemeOfOrd' [Ord α] : Inhabited (Partition.Scheme α) := ⟨Partition.hoare⟩
