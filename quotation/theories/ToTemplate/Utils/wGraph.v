(*From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Init Coq.Structures Coq.MSets Coq.Numbers.
From MetaCoq.Utils Require Import wGraph.
From Coq Require Import MSetDecide MSetInterface.

Module Nbar.
  #[export] Instance quote_le {x y} : ground_quotable (Nbar.le x y) := ltac:(cbv [Nbar.le]; exact _).
  #[export] Instance quote_lt {x y} : ground_quotable (Nbar.lt x y) := ltac:(cbv [Nbar.lt]; exact _).
End Nbar.
Export (hints) Nbar.

Module Type QuotationOfWeightedGraph (V : UsualOrderedType) (VSet : MSetInterface.S with Module E := V) (WGraph : WeightedGraphSig V VSet).
  Module qVSetFact := Nop <+ QuotationOfWFactsOn V VSet WGraph.VSetFact.
  Export (hints) qVSetFact.
  Module qVSetProp := Nop <+ QuotationOfWPropertiesOn V VSet WGraph.VSetProp.
  Export (hints) qVSetProp.
  Module qVSetDecide := Nop <+ QuotationOfWDecide VSet WGraph.VSetDecide.
  Export (hints) qVSetDecide.
  Module qEdge.
    #[export] Declare Instance qt : quotation_of WGraph.Edge.t.
    #[export] Declare Instance qeq : quotation_of WGraph.Edge.eq.
    #[export] Declare Instance qeq_equiv : quotation_of WGraph.Edge.eq_equiv.
    #[export] Declare Instance qlt : quotation_of WGraph.Edge.lt.
    #[export] Declare Instance qlt_strorder : quotation_of WGraph.Edge.lt_strorder.
    #[export] Declare Instance qlt_compat : quotation_of WGraph.Edge.lt_compat.
    #[export] Declare Instance qcompare : quotation_of WGraph.Edge.compare.
    #[export] Declare Instance qcompare_spec : quotation_of WGraph.Edge.compare_spec.
    #[export] Declare Instance qeq_dec : quotation_of WGraph.Edge.eq_dec.
    #[export] Declare Instance qeqb : quotation_of WGraph.Edge.eqb.
    #[export] Declare Instance qeq_leibniz : quotation_of WGraph.Edge.eq_leibniz.
  End qEdge.
  Export (hints) qEdge.
  Module qEdgeSet:= MSetAVL.Make Edge.
  Module qEdgeSetFact := WFactsOn Edge EdgeSet.
  Module qEdgeSetProp := WPropertiesOn Edge EdgeSet.
  Module qEdgeSetDecide := WDecide (EdgeSet).

  Module qEdgeSet.
         Module EdgeSetFact
         Module EdgeSetProp
         Module EdgeSetDecide
         Module Subgraph1
         Module IsFullSubgraph
         Module RelabelWrtEdge
  #[export] Declare Instance qVSet_add_remove : quotation_of WGraph.VSet_add_remove.
  #[export] Declare Instance qVSet_remove_add : quotation_of WGraph.VSet_remove_add.
  #[export] Declare Instance qVSet_add_add : quotation_of WGraph.VSet_add_add.
  #[export] Declare Instance qVSet_add_add_same : quotation_of WGraph.VSet_add_add_same.
  #[export] Declare Instance qDisjoint : quotation_of WGraph.Disjoint.
  #[export] Declare Instance qDisjointAdd : quotation_of WGraph.DisjointAdd.
  #[export] Declare Instance qDisjointAdd_add1 : quotation_of WGraph.DisjointAdd_add1.
  #[export] Declare Instance qDisjointAdd_add2 : quotation_of WGraph.DisjointAdd_add2.
  #[export] Declare Instance qDisjointAdd_add3 : quotation_of WGraph.DisjointAdd_add3.
  #[export] Declare Instance qDisjointAdd_remove : quotation_of WGraph.DisjointAdd_remove.
  #[export] Declare Instance qDisjointAdd_Subset : quotation_of WGraph.DisjointAdd_Subset.
  #[export] Declare Instance qDisjointAdd_union : quotation_of WGraph.DisjointAdd_union.
  #[export] Declare Instance qDisjointAdd_remove1 : quotation_of WGraph.DisjointAdd_remove1.
  #[export] Declare Instance qAdd_Proper : quotation_of WGraph.Add_Proper.
  #[export] Declare Instance qDisjointAdd_Proper : quotation_of WGraph.DisjointAdd_Proper.
  #[export] Declare Instance qAdd_In : quotation_of WGraph.Add_In.
  #[export] Declare Instance qAdd_Add : quotation_of WGraph.Add_Add.
  #[export] Declare Instance qDisjoint_DisjointAdd : quotation_of WGraph.Disjoint_DisjointAdd.
  #[export] Declare Instance qDisjointAdd_remove_add : quotation_of WGraph.DisjointAdd_remove_add.
  #[export] Declare Instance qDisjointAdd_Equal : quotation_of WGraph.DisjointAdd_Equal.
  #[export] Declare Instance qDisjointAdd_Equal_l : quotation_of WGraph.DisjointAdd_Equal_l.
  #[export] Declare Instance qDisjointAdd_remove_inv : quotation_of WGraph.DisjointAdd_remove_inv.
  #[export] Declare Instance qt : quotation_of WGraph.t.
  #[export] Declare Instance qV : quotation_of WGraph.V.
  #[export] Declare Instance qE : quotation_of WGraph.E.
  #[export] Declare Instance qs : quotation_of WGraph.s.
  #[export] Declare Instance qe_source : quotation_of WGraph.e_source.
  #[export] Declare Instance qe_target : quotation_of WGraph.e_target.
  #[export] Declare Instance qe_weight : quotation_of WGraph.e_weight.
  #[export] Declare Instance qopp_edge : quotation_of WGraph.opp_edge.
  #[export] Declare Instance qlabelling : quotation_of WGraph.labelling.
  #[export] Declare Instance qadd_node : quotation_of WGraph.add_node.
  #[export] Declare Instance qadd_edge : quotation_of WGraph.add_edge.
  #[export] Declare Instance qEdgeOf : quotation_of WGraph.EdgeOf.
  #[export] Declare Instance qPathOf : inductive_quotation_of WGraph.PathOf.
  #[export] Declare Instance qPathOf_rect : quotation_of WGraph.PathOf_rect.
  #[export] Declare Instance qPathOf_ind : quotation_of WGraph.PathOf_ind.
  #[export] Declare Instance qPathOf_rec : quotation_of WGraph.PathOf_rec.
  #[export] Declare Instance qPathOf_sind : quotation_of WGraph.PathOf_sind.
  #[export] Declare Instance qweight : quotation_of WGraph.weight.
  #[export] Declare Instance qnodes : quotation_of WGraph.nodes.
  #[export] Declare Instance qconcat : quotation_of WGraph.concat.
  #[export] Declare Instance qlength : quotation_of WGraph.length.
  #[export] Declare Instance qinvariants : inductive_quotation_of WGraph.invariants.
  #[export] Declare Instance qedges_vertices : quotation_of WGraph.edges_vertices.
  #[export] Declare Instance qsource_vertex : quotation_of WGraph.source_vertex.
  #[export] Declare Instance qsource_pathOf : quotation_of WGraph.source_pathOf.
  #[export] Declare Instance qPosPathOf : quotation_of WGraph.PosPathOf.
  #[export] Declare Instance qacyclic_no_loop : quotation_of WGraph.acyclic_no_loop.
  #[export] Declare Instance qBuild_acyclic_no_loop : quotation_of WGraph.Build_acyclic_no_loop.
  #[export] Declare Instance qacyclic_no_loop' : quotation_of WGraph.acyclic_no_loop'.
  #[export] Declare Instance qacyclic_no_loop_loop' : quotation_of WGraph.acyclic_no_loop_loop'.
  #[export] Declare Instance qcorrect_labelling : quotation_of WGraph.correct_labelling.
  #[export] Declare Instance qleq_vertices : quotation_of WGraph.leq_vertices.
  #[export] Declare Instance qSPath : inductive_quotation_of WGraph.SPath.
  #[export] Declare Instance qSPath_rect : quotation_of WGraph.SPath_rect.
  #[export] Declare Instance qSPath_ind : quotation_of WGraph.SPath_ind.
  #[export] Declare Instance qSPath_rec : quotation_of WGraph.SPath_rec.
  #[export] Declare Instance qSPath_sind : quotation_of WGraph.SPath_sind.
  #[export] Declare Instance qSPath_sig : quotation_of WGraph.SPath_sig.
  #[export] Declare Instance qSPath_sig_pack : quotation_of WGraph.SPath_sig_pack.
  #[export] Declare Instance qSPath_Signature : quotation_of WGraph.SPath_Signature.
  #[export] Declare Instance qNoConfusion_SPath : quotation_of WGraph.NoConfusion_SPath.
  #[export] Declare Instance qnoConfusion_SPath_obligation_1 : quotation_of WGraph.noConfusion_SPath_obligation_1.
  #[export] Declare Instance qnoConfusion_SPath_obligation_2 : quotation_of WGraph.noConfusion_SPath_obligation_2.
  #[export] Declare Instance qnoConfusion_SPath_obligation_3 : quotation_of WGraph.noConfusion_SPath_obligation_3.
  #[export] Declare Instance qnoConfusion_SPath_obligation_4 : quotation_of WGraph.noConfusion_SPath_obligation_4.
  #[export] Declare Instance qNoConfusionPackage_SPath : quotation_of WGraph.NoConfusionPackage_SPath.
  #[export] Declare Instance qto_pathOf : quotation_of WGraph.to_pathOf.
  #[export] Declare Instance qsweight : quotation_of WGraph.sweight.
  #[export] Declare Instance qsweight_weight : quotation_of WGraph.sweight_weight.
  #[export] Declare Instance qis_simple : quotation_of WGraph.is_simple.
  #[export] Declare Instance qto_simple_obligation_1 : quotation_of WGraph.to_simple_obligation_1.
  #[export] Declare Instance qto_simple_obligation_2 : quotation_of WGraph.to_simple_obligation_2.
  #[export] Declare Instance qto_simple : quotation_of WGraph.to_simple.
  #[export] Declare Instance qweight_concat : quotation_of WGraph.weight_concat.
  #[export] Declare Instance qadd_end : quotation_of WGraph.add_end.
  #[export] Declare Instance qweight_add_end : quotation_of WGraph.weight_add_end.
  #[export] Declare Instance qSPath_sub : quotation_of WGraph.SPath_sub.
  #[export] Declare Instance qweight_SPath_sub : quotation_of WGraph.weight_SPath_sub.
  #[export] Declare Instance qsconcat_obligation_1 : quotation_of WGraph.sconcat_obligation_1.
  #[export] Declare Instance qsconcat_obligation_2 : quotation_of WGraph.sconcat_obligation_2.
  #[export] Declare Instance qsconcat_obligation_3 : quotation_of WGraph.sconcat_obligation_3.
  #[export] Declare Instance qsconcat : quotation_of WGraph.sconcat.
  #[export] Declare Instance qsweight_sconcat : quotation_of WGraph.sweight_sconcat.
  #[export] Declare Instance qsnodes : quotation_of WGraph.snodes.
  #[export] Declare Instance qsplit : quotation_of WGraph.split.
  #[export] Declare Instance qweight_split : quotation_of WGraph.weight_split.
  #[export] Declare Instance qsplit' : quotation_of WGraph.split'.
  #[export] Declare Instance qweight_split' : quotation_of WGraph.weight_split'.
  #[export] Declare Instance qspath_one : quotation_of WGraph.spath_one.
  #[export] Declare Instance qsimplify_aux1 : quotation_of WGraph.simplify_aux1.
  #[export] Declare Instance qsimplify_aux2 : quotation_of WGraph.simplify_aux2.
  #[export] Declare Instance qsimplify_aux3 : quotation_of WGraph.simplify_aux3.
  #[export] Declare Instance qsimplify : quotation_of WGraph.simplify.
  #[export] Declare Instance qweight_simplify : quotation_of WGraph.weight_simplify.
  #[export] Declare Instance qsuccs : quotation_of WGraph.succs.
  #[export] Declare Instance qlsp00 : quotation_of WGraph.lsp00.
  #[export] Declare Instance qlsp0 : quotation_of WGraph.lsp0.
  #[export] Declare Instance qlsp0_eq : quotation_of WGraph.lsp0_eq.
  #[export] Declare Instance qlsp00_fast : quotation_of WGraph.lsp00_fast.
  #[export] Declare Instance qfold_left_map : quotation_of WGraph.fold_left_map.
  #[export] Declare Instance qfold_left_filter : quotation_of WGraph.fold_left_filter.
  #[export] Declare Instance qfold_left_proper : quotation_of WGraph.fold_left_proper.
  #[export] Declare Instance qfold_left_equiv : quotation_of WGraph.fold_left_equiv.
  #[export] Declare Instance qlsp00_optim : quotation_of WGraph.lsp00_optim.
  #[export] Declare Instance qlsp_fast : quotation_of WGraph.lsp_fast.
  #[export] Declare Instance qlsp : quotation_of WGraph.lsp.
  #[export] Declare Instance qlsp_optim : quotation_of WGraph.lsp_optim.
  #[export] Declare Instance qlsp0_VSet_Equal : quotation_of WGraph.lsp0_VSet_Equal.
  #[export] Declare Instance qlsp0_spec_le : quotation_of WGraph.lsp0_spec_le.
  #[export] Declare Instance qlsp0_spec_eq : quotation_of WGraph.lsp0_spec_eq.
  #[export] Declare Instance qlsp0_spec_eq0 : quotation_of WGraph.lsp0_spec_eq0.
  #[export] Declare Instance qcorrect_labelling_PathOf : quotation_of WGraph.correct_labelling_PathOf.
  #[export] Declare Instance qcorrect_labelling_lsp : quotation_of WGraph.correct_labelling_lsp.
  #[export] Declare Instance qacyclic_labelling : quotation_of WGraph.acyclic_labelling.
  #[export] Declare Instance qlsp0_triangle_inequality : quotation_of WGraph.lsp0_triangle_inequality.
  #[export] Declare Instance qis_nonpos : quotation_of WGraph.is_nonpos.
  #[export] Declare Instance qis_nonpos_spec : quotation_of WGraph.is_nonpos_spec.
  #[export] Declare Instance qis_nonpos_nbar : quotation_of WGraph.is_nonpos_nbar.
  #[export] Declare Instance qlsp0_sub : quotation_of WGraph.lsp0_sub.
  #[export] Declare Instance qsnodes_Subset : quotation_of WGraph.snodes_Subset.
  #[export] Declare Instance qreduce : quotation_of WGraph.reduce.
  #[export] Declare Instance qsimplify2 : quotation_of WGraph.simplify2.
  #[export] Declare Instance qweight_reduce : quotation_of WGraph.weight_reduce.
  #[export] Declare Instance qweight_simplify2 : quotation_of WGraph.weight_simplify2.
  #[export] Declare Instance qnodes_subset : quotation_of WGraph.nodes_subset.
  #[export] Declare Instance qsimplify2' : quotation_of WGraph.simplify2'.
  #[export] Declare Instance qweight_simplify2' : quotation_of WGraph.weight_simplify2'.
  #[export] Declare Instance qlsp_s : quotation_of WGraph.lsp_s.
  #[export] Declare Instance qSPath_In : quotation_of WGraph.SPath_In.
  #[export] Declare Instance qSPath_In' : quotation_of WGraph.SPath_In'.
  #[export] Declare Instance qPathOf_In : quotation_of WGraph.PathOf_In.
  #[export] Declare Instance qacyclic_lsp0_xx : quotation_of WGraph.acyclic_lsp0_xx.
  #[export] Declare Instance qto_label : quotation_of WGraph.to_label.
  #[export] Declare Instance qZ_of_to_label : quotation_of WGraph.Z_of_to_label.
  #[export] Declare Instance qZ_of_to_label_s : quotation_of WGraph.Z_of_to_label_s.
  #[export] Declare Instance qlsp_correctness : quotation_of WGraph.lsp_correctness.
  #[export] Declare Instance qlsp_codistance : quotation_of WGraph.lsp_codistance.
  #[export] Declare Instance qlsp_sym : quotation_of WGraph.lsp_sym.
  #[export] Declare Instance qle_Some_lsp : quotation_of WGraph.le_Some_lsp.
  #[export] Declare Instance qsource_bottom : quotation_of WGraph.source_bottom.
  #[export] Declare Instance qlsp_to_s : quotation_of WGraph.lsp_to_s.
  #[export] Declare Instance qlsp_xx_acyclic : quotation_of WGraph.lsp_xx_acyclic.
  #[export] Declare Instance qVSet_Forall_reflect : quotation_of WGraph.VSet_Forall_reflect.
  #[export] Declare Instance qreflect_logically_equiv : quotation_of WGraph.reflect_logically_equiv.
  #[export] Declare Instance qis_acyclic : quotation_of WGraph.is_acyclic.
  #[export] Declare Instance qacyclic_caract1 : quotation_of WGraph.acyclic_caract1.
  #[export] Declare Instance qacyclic_caract2 : quotation_of WGraph.acyclic_caract2.
  #[export] Declare Instance qis_acyclic_spec : quotation_of WGraph.is_acyclic_spec.
  #[export] Declare Instance qZle_opp : quotation_of WGraph.Zle_opp.
  #[export] Declare Instance qZle_opp' : quotation_of WGraph.Zle_opp'.
  #[export] Declare Instance qlsp_xx : quotation_of WGraph.lsp_xx.
  #[export] Declare Instance qedge_pathOf : quotation_of WGraph.edge_pathOf.
  #[export] Declare Instance qZ_of_to_label_pos : quotation_of WGraph.Z_of_to_label_pos.
  #[export] Declare Instance qto_label_max : quotation_of WGraph.to_label_max.
  #[export] Declare Instance qlsp_from_source : quotation_of WGraph.lsp_from_source.
  #[export] Declare Instance qlsp_to_source : quotation_of WGraph.lsp_to_source.
  #[export] Declare Instance qlsp_source_max : quotation_of WGraph.lsp_source_max.
  #[export] Declare Instance qis_acyclic_correct : quotation_of WGraph.is_acyclic_correct.
  #[export] Declare Instance qG' : quotation_of WGraph.G'.
  #[export] Declare Instance qto_G' : quotation_of WGraph.to_G'.
  #[export] Declare Instance qto_G'_weight : quotation_of WGraph.to_G'_weight.
  #[export] Declare Instance qfrom_G'_path : quotation_of WGraph.from_G'_path.
  #[export] Declare Instance qfrom_G'_path_weight : quotation_of WGraph.from_G'_path_weight.
  #[export] Declare Instance qfrom_G' : quotation_of WGraph.from_G'.
  #[export] Declare Instance qfrom_G'_weight : quotation_of WGraph.from_G'_weight.
  #[export] Declare Instance qlsp_pathOf : quotation_of WGraph.lsp_pathOf.
  #[export] Declare Instance qHI' : quotation_of WGraph.HI'.
  #[export] Declare Instance qHG' : quotation_of WGraph.HG'.
  #[export] Declare Instance qlsp_G'_yx : quotation_of WGraph.lsp_G'_yx.
  #[export] Declare Instance qlsp_G'_sx : quotation_of WGraph.lsp_G'_sx.
  #[export] Declare Instance qcorrect_labelling_lsp_G' : quotation_of WGraph.correct_labelling_lsp_G'.
  #[export] Declare Instance qsto_G' : quotation_of WGraph.sto_G'.
  #[export] Declare Instance qsto_G'_weight : quotation_of WGraph.sto_G'_weight.
  #[export] Declare Instance qlsp_G'_incr : quotation_of WGraph.lsp_G'_incr.
  #[export] Declare Instance qlsp_G'_spec_left : quotation_of WGraph.lsp_G'_spec_left.
  #[export] Declare Instance qSPath_sets : quotation_of WGraph.SPath_sets.
  #[export] Declare Instance qPathOf_add_end : quotation_of WGraph.PathOf_add_end.
  #[export] Declare Instance qPathOf_add_end_weight : quotation_of WGraph.PathOf_add_end_weight.
  #[export] Declare Instance qnegbe : quotation_of WGraph.negbe.
  #[export] Declare Instance qIn_nodes_app_end : quotation_of WGraph.In_nodes_app_end.
  #[export] Declare Instance qpathOf_add_end_simpl : quotation_of WGraph.pathOf_add_end_simpl.
  #[export] Declare Instance qleq_vertices_caract0 : quotation_of WGraph.leq_vertices_caract0.
  #[export] Declare Instance qlsp_vset_in : quotation_of WGraph.lsp_vset_in.
  #[export] Declare Instance qleq_vertices_caract_subproof : quotation_of WGraph.leq_vertices_caract_subproof.
  #[export] Declare Instance qleq_vertices_caract : quotation_of WGraph.leq_vertices_caract.
  #[export] Declare Instance qleqb_vertices : quotation_of WGraph.leqb_vertices.
  #[export] Declare Instance qleqb_vertices_correct : quotation_of WGraph.leqb_vertices_correct.
  #[export] Declare Instance qedge_map : quotation_of WGraph.edge_map.
  #[export] Declare Instance qedge_map_spec1 : quotation_of WGraph.edge_map_spec1.
  #[export] Declare Instance qedge_map_spec2 : quotation_of WGraph.edge_map_spec2.
  #[export] Declare Instance qdiff : quotation_of WGraph.diff.
  #[export] Declare Instance qrelabel : quotation_of WGraph.relabel.
  #[export] Declare Instance qrelabel_weight : quotation_of WGraph.relabel_weight.
  #[export] Declare Instance qrelabel_lsp : quotation_of WGraph.relabel_lsp.
  #[export] Declare Instance qacyclic_relabel : quotation_of WGraph.acyclic_relabel.
  #[export] Declare Instance qrelabel_path : quotation_of WGraph.relabel_path.
  #[export] Declare Instance qinvariants_relabel : quotation_of WGraph.invariants_relabel.
  #[export] Declare Instance qrelabel_map : quotation_of WGraph.relabel_map.
  #[export] Declare Instance qrelabel_on : quotation_of WGraph.relabel_on.
  #[export] Declare Instance qweight_inverse : quotation_of WGraph.weight_inverse.
  #[export] Declare Instance qsweight_inverse : quotation_of WGraph.sweight_inverse.
  #[export] Declare Instance qacyclic_no_sloop : quotation_of WGraph.acyclic_no_sloop.
  #[export] Declare Instance qacyclic_no_loop_sloop : quotation_of WGraph.acyclic_no_loop_sloop.
  #[export] Declare Instance qDisjointAdd_add4 : quotation_of WGraph.DisjointAdd_add4.
  #[export] Declare Instance qDisjointAdd_In : quotation_of WGraph.DisjointAdd_In.
  #[export] Declare Instance qreroot_spath_aux1 : quotation_of WGraph.reroot_spath_aux1.
  #[export] Declare Instance qreroot_spath_aux2 : quotation_of WGraph.reroot_spath_aux2.
  #[export] Declare Instance qreroot_spath_aux3 : quotation_of WGraph.reroot_spath_aux3.
  #[export] Declare Instance qreroot_spath_aux : quotation_of WGraph.reroot_spath_aux.
  #[export] Declare Instance qreroot_spath : quotation_of WGraph.reroot_spath.
  #[export] Declare Instance qmap_path : quotation_of WGraph.map_path.
  #[export] Declare Instance qmap_path_equation_1 : quotation_of WGraph.map_path_equation_1.
  #[export] Declare Instance qmap_path_equation_2 : quotation_of WGraph.map_path_equation_2.
  #[export] Declare Instance qmap_path_graph : inductive_quotation_of WGraph.map_path_graph.
  #[export] Declare Instance qmap_path_graph_rect : quotation_of WGraph.map_path_graph_rect.
  #[export] Declare Instance qmap_path_graph_correct : quotation_of WGraph.map_path_graph_correct.
  #[export] Declare Instance qmap_path_elim : quotation_of WGraph.map_path_elim.
  #[export] Declare Instance qFunctionalElimination_map_path : quotation_of WGraph.FunctionalElimination_map_path.
  #[export] Declare Instance qFunctionalInduction_map_path : quotation_of WGraph.FunctionalInduction_map_path.
  #[export] Declare Instance qweight_map_path1 : quotation_of WGraph.weight_map_path1.
  #[export] Declare Instance qweight_map_path2 : quotation_of WGraph.weight_map_path2.
  #[export] Declare Instance qmap_spath : quotation_of WGraph.map_spath.
  #[export] Declare Instance qmap_spath_equation_1 : quotation_of WGraph.map_spath_equation_1.
  #[export] Declare Instance qmap_spath_equation_2 : quotation_of WGraph.map_spath_equation_2.
  #[export] Declare Instance qmap_spath_graph : inductive_quotation_of WGraph.map_spath_graph.
  #[export] Declare Instance qmap_spath_graph_rect : quotation_of WGraph.map_spath_graph_rect.
  #[export] Declare Instance qmap_spath_graph_correct : quotation_of WGraph.map_spath_graph_correct.
  #[export] Declare Instance qmap_spath_elim : quotation_of WGraph.map_spath_elim.
  #[export] Declare Instance qFunctionalElimination_map_spath : quotation_of WGraph.FunctionalElimination_map_spath.
  #[export] Declare Instance qFunctionalInduction_map_spath : quotation_of WGraph.FunctionalInduction_map_spath.
  #[export] Declare Instance qweight_map_spath1 : quotation_of WGraph.weight_map_spath1.
  #[export] Declare Instance qweight_map_spath2 : quotation_of WGraph.weight_map_spath2.
  #[export] Declare Instance qlsp_map_path2 : quotation_of WGraph.lsp_map_path2.
  #[export] Declare Instance qlsp_edge : quotation_of WGraph.lsp_edge.
  #[export] Declare Instance qfirst_in_clause_2 : quotation_of WGraph.first_in_clause_2.
  #[export] Declare Instance qfirst_in : quotation_of WGraph.first_in.
  #[export] Declare Instance qfirst_in_equation_1 : quotation_of WGraph.first_in_equation_1.
  #[export] Declare Instance qfirst_in_equation_2 : quotation_of WGraph.first_in_equation_2.
  #[export] Declare Instance qfirst_in_clause_2_equation_1 : quotation_of WGraph.first_in_clause_2_equation_1.
  #[export] Declare Instance qfirst_in_clause_2_equation_2 : quotation_of WGraph.first_in_clause_2_equation_2.
  #[export] Declare Instance qfirst_in_graph : inductive_quotation_of WGraph.first_in_graph.
  #[export] Declare Instance qfirst_in_clause_2_graph_mut : quotation_of WGraph.first_in_clause_2_graph_mut.
  #[export] Declare Instance qfirst_in_graph_mut : quotation_of WGraph.first_in_graph_mut.
  #[export] Declare Instance qfirst_in_graph_rect : quotation_of WGraph.first_in_graph_rect.
  #[export] Declare Instance qfirst_in_graph_correct : quotation_of WGraph.first_in_graph_correct.
  #[export] Declare Instance qfirst_in_elim : quotation_of WGraph.first_in_elim.
  #[export] Declare Instance qFunctionalElimination_first_in : quotation_of WGraph.FunctionalElimination_first_in.
  #[export] Declare Instance qFunctionalInduction_first_in : quotation_of WGraph.FunctionalInduction_first_in.
  #[export] Declare Instance qfirst_in_in : quotation_of WGraph.first_in_in.
  #[export] Declare Instance qfirst_in_first : quotation_of WGraph.first_in_first.
  #[export] Declare Instance qfrom1 : quotation_of WGraph.from1.
  #[export] Declare Instance qfrom2 : quotation_of WGraph.from2.
  #[export] Declare Instance qrelabel_on_lsp_G1 : quotation_of WGraph.relabel_on_lsp_G1.
  #[export] Declare Instance qrelabel_on_lsp_G2 : quotation_of WGraph.relabel_on_lsp_G2.
  #[export] Declare Instance qweight_from1 : quotation_of WGraph.weight_from1.
  #[export] Declare Instance qweight_from2 : quotation_of WGraph.weight_from2.
  #[export] Declare Instance qrelabel_on_invariants : quotation_of WGraph.relabel_on_invariants.
  #[export] Declare Instance qsweight_relabel_on_G1 : quotation_of WGraph.sweight_relabel_on_G1.
  #[export] Declare Instance qsweight_relabel_on_G2 : quotation_of WGraph.sweight_relabel_on_G2.
  #[export] Declare Instance qacyclic_relabel_on : quotation_of WGraph.acyclic_relabel_on.
  #[export] Declare Instance qSPath_direct_subterm : inductive_quotation_of WGraph.SPath_direct_subterm.
  #[export] Declare Instance qSPath_direct_subterm_ind : quotation_of WGraph.SPath_direct_subterm_ind.
  #[export] Declare Instance qSPath_direct_subterm_sind : quotation_of WGraph.SPath_direct_subterm_sind.
  #[export] Declare Instance qSPath_direct_subterm_sig : quotation_of WGraph.SPath_direct_subterm_sig.
  #[export] Declare Instance qSPath_direct_subterm_sig_pack : quotation_of WGraph.SPath_direct_subterm_sig_pack.
  #[export] Declare Instance qSPath_direct_subterm_Signature : quotation_of WGraph.SPath_direct_subterm_Signature.
  #[export] Declare Instance qSPath_subterm : quotation_of WGraph.SPath_subterm.
  #[export] Declare Instance qwell_founded_SPath_subterm_obligation_1 : quotation_of WGraph.well_founded_SPath_subterm_obligation_1.
  #[export] Declare Instance qwell_founded_SPath_subterm : quotation_of WGraph.well_founded_SPath_subterm.
  #[export] Declare Instance qspathG1_lsp_Gl : quotation_of WGraph.spathG1_lsp_Gl.
  #[export] Declare Instance qlsp_Gl_upperbound_G1 : quotation_of WGraph.lsp_Gl_upperbound_G1.
  #[export] Declare Instance qlsp_Gl_between_G1 : quotation_of WGraph.lsp_Gl_between_G1.
  #[export] Declare Instance qsubgraph : inductive_quotation_of WGraph.subgraph.
  #[export] Declare Instance qvertices_sub : quotation_of WGraph.vertices_sub.
  #[export] Declare Instance qedges_sub : quotation_of WGraph.edges_sub.
  #[export] Declare Instance qsame_src : quotation_of WGraph.same_src.
  #[export] Declare Instance qsubgraph_on_edge : quotation_of WGraph.subgraph_on_edge.
  #[export] Declare Instance qsubgraph_acyclic : quotation_of WGraph.subgraph_acyclic.
  #[export] Declare Instance qfull_subgraph : inductive_quotation_of WGraph.full_subgraph.
  #[export] Declare Instance qis_subgraph : quotation_of WGraph.is_subgraph.
  #[export] Declare Instance qlsp_dominate : quotation_of WGraph.lsp_dominate.
  #[export] Declare Instance qreflectEq_vertices_obligation_1 : quotation_of WGraph.reflectEq_vertices_obligation_1.
  #[export] Declare Instance qreflectEq_vertices : quotation_of WGraph.reflectEq_vertices.
  #[export] Declare Instance qreflectEq_Z_obligation_1 : quotation_of WGraph.reflectEq_Z_obligation_1.
  #[export] Declare Instance qreflectEq_Z : quotation_of WGraph.reflectEq_Z.
  #[export] Declare Instance qreflectEq_nbar : quotation_of WGraph.reflectEq_nbar.
  #[export] Declare Instance qextends_labelling : quotation_of WGraph.extends_labelling.
  #[export] Declare Instance qrelabel_on_correct_labelling : quotation_of WGraph.relabel_on_correct_labelling.
  #[export] Declare Instance qextends_correct_labelling : quotation_of WGraph.extends_correct_labelling.
  #[export] Declare Instance qto_label_to_nat : quotation_of WGraph.to_label_to_nat.
  #[export] Declare Instance qlabelling_ext_lsp : quotation_of WGraph.labelling_ext_lsp.

  (qV : QuotationOfUsualOrderedType V) (qVSet : MSets.QuotationOfSets VSet).

  (MProperties : OrdPropertiesSig M) (qE : QuotationOfUsualOrderedType M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties qE).

  *)(*
Module QuoteWeightedGraph (V : UsualOrderedType) (VSet : MSetInterface.S with Module E := V) (Import W : WeightedGraphSig V VSet).
  Module Import QuoteVSet := QuoteUsualSetsOn V VSet.
  Module Import QuoteEdgeSet := QuoteMSetAVL Edge EdgeSet.

  Section with_quote.
    Context {qEdgeSet_t : quotation_of EdgeSet.t} {qV_t : quotation_of V.t} {qVSet_t : quotation_of VSet.t}
            {qVSet_In : quotation_of VSet.In} {qEdgeSet_In : quotation_of EdgeSet.In}
            {qVSet_eq_dec : quotation_of VSet.eq_dec} {qVSet_add : quotation_of VSet.add} {qEdgeSet_subset_spec : quotation_of EdgeSet.subset_spec} {qlsp : quotation_of lsp}
            {qEdgeSet_tree : inductive_quotation_of EdgeSet.Raw.tree} {qEdgeSetbst : inductive_quotation_of EdgeSet.Raw.bst} {qEdgeSet_t_ : inductive_quotation_of EdgeSet.t_}
            {qPathOf : inductive_quotation_of PathOf}
            {qSPath : inductive_quotation_of SPath}
            {qsubgraph : inductive_quotation_of subgraph} {qfull_subgraph : inductive_quotation_of full_subgraph}
            {quote_V_t : ground_quotable V.t} {quote_VSet_t : ground_quotable VSet.t}.

    #[export] Instance qEdgeSet_elt : quotation_of EdgeSet.elt := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qt : quotation_of t := ltac:(cbv [t]; exact _).
    #[export] Instance qWE : quotation_of W.E := ltac:(cbv [W.E]; exact _).
    #[export] Instance qWV : quotation_of W.V := ltac:(cbv [W.V]; exact _).
    #[export] Instance qVSetProp_Add : quotation_of VSetProp.Add := ltac:(cbv [VSetProp.Add]; exact _).
    #[export] Instance qVSet : quotation_of VSetProp.Add := ltac:(cbv [VSetProp.Add]; exact _).
    #[export] Instance quote_t : ground_quotable t := _.
    #[export] Instance quote_PathOf {G x y} : ground_quotable (@PathOf G x y) := ltac:(induction 1; exact _).
    #[export] Instance quote_SPath {G s x y} : ground_quotable (@SPath G s x y) := ltac:(induction 1; exact _).
    #[export] Instance quote_subgraph {G1 G2} : ground_quotable (@subgraph G1 G2) := ltac:(induction 1; exact _).
    #[export] Instance quote_full_subgraph {G1 G2} : ground_quotable (@full_subgraph G1 G2) := ltac:(induction 1; exact _).
  End with_quote.

  Module Import Edge.
    Definition lt_dec x y : {Edge.lt x y} + {~Edge.lt x y}.
    Proof.
      pose proof (Edge.compare_spec x y) as H.
      destruct (Edge.compare x y);
        solve [ left; inversion H; assumption
              | right; intro H'; inversion H; subst;
                eapply Edge.lt_strorder; (idtac + etransitivity); eassumption ].
    Defined.

    Section with_quote.
      Context {qV_t : quotation_of V.t} {qV_lt : quotation_of V.lt}.

      #[export] Instance qEdge_t : quotation_of Edge.t := ltac:(cbv -[quotation_of]; exact _).
      #[export] Instance qlt : quotation_of Edge.lt := ltac:(cbv [Edge.lt V.eq]; try exact _).
      #[export] Instance quote_lt {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Edge.lt x y) := ground_quotable_of_dec (@lt_dec x y).
    End with_quote.

    Module Export Instances.
      #[export] Existing Instances
       quote_lt
      .
    End Instances.
  End Edge.
  Module Export Instances.
    Export QuoteVSet.Instances.
    Export QuoteEdgeSet.Instances.
    Export Edge.Instances.
    #[export] Existing Instances
     quote_t
     quote_PathOf
     quote_SPath
     quote_subgraph
     quote_full_subgraph
    .
  End Instances.
End QuoteWeightedGraph.
*)
