import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Proofs.Chips.ProtectedStore
import SP1Clean.Native.Operations.WritePermission

/-! # Local AIR with explicit ROM write protection

Four instruction components acquire byte-permission requests, and one fixed-interval provider
supplies them. The complete source verifier and all other tables are retained. This is the native
assembly intended for the capstone. `ProtectedLocalCoreExecution` derives ordinary ROM preservation
from its additional ledger; active host effects and complete execution reconstruction remain open.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The four store positions in the shared instruction inventory, after the seven boundary rows. -/
def tables (image : ProgramImage) (source : ExecutionSnapshot) : List (Component (ZMod p)) :=
  let stores := LocalCore.tables image source
    |>.set 25 { circuit := ProtectedStore.byte }
    |>.set 26 { circuit := ProtectedStore.half }
    |>.set 27 { circuit := ProtectedStore.word }
    |>.set 28 { circuit := ProtectedStore.double }
  stores ++ [{ circuit := WritePermissionProvider.circuit image }]

/-- Permission wrappers keep the original stores' canonical data keys. -/
theorem tables_names (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).map (·.circuit.name) =
      (LocalCore.tables (p := p) image source).map (·.circuit.name) ++ ["sp1.native.write_permission"] := by
  rfl

/-- The provider adds one new name to the unchanged local inventory. -/
theorem tables_unique_names (image : ProgramImage) (source : ExecutionSnapshot) :
    ((tables (p := p) image source).map (·.circuit.name)).Nodup := by
  rw [tables_names, List.nodup_append]
  refine ⟨(LocalCore.baseEnsemble image source).unique_names, by simp, ?_⟩
  simp only [LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
    SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
    MemorySnapshot.registerTable, StaticTable.ofRows]
  exact of_decide_eq_true rfl

def ensemble (image : ProgramImage) (source : ExecutionSnapshot) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source
  unique_names := tables_unique_names image source
  channels := WritePermissionProvider.channel.toRaw :: (LocalCore.ensemble image source).channels
  verifier := (LocalCore.ensemble image source).verifier

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).length = 62 := by
  simp only [tables, List.length_append, List.length_set, List.length_singleton, LocalCore.tables_length]

end SP1Clean.Soundness.ProtectedLocalCore
