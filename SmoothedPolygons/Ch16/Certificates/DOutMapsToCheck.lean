module

public import SmoothedPolygons.Ch16.Certificates.DOutMapsToData

/-!
# `F(𝒟₀₀) ⊆ 𝒟₀₀`: the kernel check

The certificate tree of `DOutMapsToData.lean` passes the interval check, by `decide +kernel`
(no compiled code, no extra axiom), one theorem per subtree.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutMaps

theorem check_0l_2l_1l : checkTree (((root.lower 0).lower 2).lower 1) tree_0l_2l_1l = true := by
  decide +kernel

theorem check_0l_2l_1u : checkTree (((root.lower 0).lower 2).upper 1) tree_0l_2l_1u = true := by
  decide +kernel

theorem check_0l_2u_1l : checkTree (((root.lower 0).upper 2).lower 1) tree_0l_2u_1l = true := by
  decide +kernel

theorem check_0l_2u_1u : checkTree (((root.lower 0).upper 2).upper 1) tree_0l_2u_1u = true := by
  decide +kernel

theorem check_0u_2l_1l : checkTree (((root.upper 0).lower 2).lower 1) tree_0u_2l_1l = true := by
  decide +kernel

theorem check_0u_2l_1u : checkTree (((root.upper 0).lower 2).upper 1) tree_0u_2l_1u = true := by
  decide +kernel

theorem check_0u_2u_1l : checkTree (((root.upper 0).upper 2).lower 1) tree_0u_2u_1l = true := by
  decide +kernel

theorem check_0u_2u_1u : checkTree (((root.upper 0).upper 2).upper 1) tree_0u_2u_1u = true := by
  decide +kernel

end SmoothedPolygons.TriFuller.DOutMaps
