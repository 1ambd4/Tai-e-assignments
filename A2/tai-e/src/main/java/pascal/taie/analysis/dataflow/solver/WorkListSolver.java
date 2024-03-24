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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import soot.util.ArraySet;

import java.util.ArrayDeque;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // OUT[entry] = ??
        // for (each basic block B\entry)
        //     OUT[B] = ??
        // WorkList <- all basic blocks
        // while (WorkList is not empty)
        //     Pick a basic block B from WorkList
        //     Old_OUT = OUT[B]
        //     IN[B] = Meet OUT[P], for P is a predecessor of B
        //     OUT[B] = genB Meet (IN[B] - killB)
        //     if Old_OUT != OUT[B]
        //         Add all successors of B to WorkList

        Queue<Node> workList = new ArrayDeque<Node>();
        // WorkList <- all basic blocks
        for (Node node : cfg) {
            workList.add(node);
        }

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in = result.getInFact(node);
            Fact out = result.getOutFact(node);

            // IN[B] = Meet OUT[P], for P is a predecessor of B
            for (Node pre : cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pre), in);
            }

            // OUT[B] = genB Meet (IN[B] - killB)
            // for here, Meet is not Set Operation but transfer function
            if (analysis.transferNode(node, in, out)) {
                // if Old_OUT != OUT[B]
                // Add all successors of B to WorkList
                for (Node succ : cfg.getSuccsOf(node)) {
                    workList.add(succ);
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
