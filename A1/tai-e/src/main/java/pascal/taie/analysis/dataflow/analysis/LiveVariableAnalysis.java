/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;
import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    /**
     * @return true if this analysis is forward, otherwise false.
     */
    @Override
    public boolean isForward() {
        // Live Variable Analysis is more convenient with backward analysis.
        return false;
    }

    /**
     * @return new fact in boundary conditions, i.e., the fact for
     * entry (exit) node in forward (backward) analysis.
     */
    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // Semantically, what we want to know is whether there is a variable alive at 
        // a certain program point. Obviously IN[exit] should be initialized to empty.
        return new SetFact<Var>();
    }

    /**
     * @return new initial fact for non-boundary nodes.
     */
    @Override
    public SetFact<Var> newInitialFact() {
        // Live Variable Analysis is a May Analysis.
        // So initial fact shoud be initialized to empty.
        return new SetFact<Var>();
    }

    /**
     * Meets a fact into another (target) fact.
     * This function will be used to handle control-flow confluences.
     */
    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // Since it is a may analysis, meet mean union here.
        // OUT[B] = Union IN[S] (for S is successor of B)
        target.union(fact);
    }

    /**
     * Node Transfer function for the analysis.
     * The function transfers data-flow from in (out) fact to out (in) fact
     * for forward (backward) analysis.
     *
     * @return true if the transfer changed the out (in) fact, otherwise false.
     */
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // IN[B] = use Union (OUT[B] - def)
        List<RValue> use = stmt.getUses();
        Optional<LValue> def = stmt.getDef();
        boolean changed = false;

        SetFact<Var> tmp = out.copy();
        if (def.isPresent() && def.get() instanceof Var defVar) {
            tmp.remove(defVar);
        }

        for (RValue e : use) {
            if (e instanceof Var useVar) {
                tmp.add(useVar);
            }
        }

        if (!in.equals(tmp)) {
            changed = true;
            in.set(tmp);
        }

        return changed;
    }
}
