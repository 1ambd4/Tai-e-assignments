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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    /**
     * @return true if this analysis is forward, otherwise false.
     */
    @Override
    public boolean isForward() {
        return true;
    }

    /**
     * @return new fact in boundary conditions, i.e., the fact for
     * entry (exit) node in forward (backward) analysis.
     */
    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // Constant propagation is a forward analysis, so boundary fact entry init to empty?
        CPFact fact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    /**
     * @return new initial fact for non-boundary nodes.
     */
    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    /**
     * Meets a fact into another (target) fact.
     * This function will be used to handle control-flow confluences.
     */
    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            // If var not in target, target.get() will return UNDEF.
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // Meet rule
        // 1. NAC   meet v  = NAC
        // 2. UNDEF meet v  = v, since uninitialized variables are not focus in our constant propagation analysis
        // 3. c     meet v  = NAC
        // 4. c     meet c  = c
        // 5. c1    meet c2 = NAC

        // rule 1: NAC meet v = NAC
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        // rule 2: UNDEF meet v = v
        if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        }

        // rule 4: c meet c = c
        if (v1.getConstant() == v2.getConstant()) {
            return Value.makeConstant(v1.getConstant());
        }

        // rule 3: c  meet v  = NAC
        // rule 5: c1 meet c2 = NAC
        return Value.getNAC();
    }

    /**
     * Node Transfer function for the analysis.
     * The function transfers data-flow from in (out) fact to out (in) fact
     * for forward (backward) analysis.
     *
     * @return true if the transfer changed the out (in) fact, otherwise false.
     */
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // F: OUT[s] = gen U (IN[s] - {(x,_)})
        if (stmt instanceof DefinitionStmt<?,?>) {
            LValue lv = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rv = ((DefinitionStmt<?, ?>) stmt).getRValue();
            if (lv instanceof Var && canHoldInt((Var)lv)) {
                CPFact tmp = in.copy();
                tmp.update((Var)lv, evaluate(rv, in));
                return out.copyFrom(tmp);
            }
        }
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // exp: x = c;
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }

        // exp: x = y
        if (exp instanceof Var var) {
            return in.get(var);
        }

        // if not BinaryExp, like function call, for safe, just return NAC.
        if (!(exp instanceof BinaryExp)) {
            return Value.getNAC();
        }

        // exp: x = oprand1 op oprand2
        Var oprand1 = ((BinaryExp) exp).getOperand1();
        var oprand2 = ((BinaryExp) exp).getOperand2();
        // f(y,z) = val(y) op val(z), if val(y) and val(z) are constants
        //          NAC, if val(y) or val(z) is NAC
        //          UNDEF, otherwise
        Value value1 = in.get(oprand1);
        Value value2 = in.get(oprand2);

        // Oops! Wrong here, AC 51/52.
        // https://github.com/pascal-lab/Tai-e-assignments/issues/2
        // If value2 is zero and op is DIV or REM, must return UNDEF.
        // Think here, if value1 is not constant, other word, value1 is NAC or UNDEF.
        // It just returned that.
        // But noticed, if here value2 is 0, and op is DIV or REM, it must return UNDEF.
        // So, must check if value2 is equal 0 or not.
        // But, how can solve this bug elegantly?

        // Not elegantly, but work, :)
        // Be sure that constant2 is not zero if op is div or rem.
        if (value2.isConstant() && value2.getConstant() == 0) {
            if (exp instanceof ArithmeticExp arithmeticExp) {
                if (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM) {
                    return Value.getUndef();
                }
            }
        }

        // if value1 or value2 is not constant, just return that.
        if (!value1.isConstant()) {
            return value1;
        } else if (!value2.isConstant()) {
            return value2;
        }

        // if value1 and value2 all constant, then evaluate it.
        int constant1 = value1.getConstant();
        int constant2 = value2.getConstant();
        if (exp instanceof ArithmeticExp arithmeticExp) {
            return switch (arithmeticExp.getOperator()) {
                case ADD -> Value.makeConstant(constant1 + constant2);
                case SUB -> Value.makeConstant(constant1 - constant2);
                case MUL -> Value.makeConstant(constant1 * constant2);
                case DIV -> Value.makeConstant(constant1 / constant2);
                case REM -> Value.makeConstant(constant1 % constant2);
            };
        } else if (exp instanceof ConditionExp conditionExp) {
            return switch (conditionExp.getOperator()) {
                case EQ -> Value.makeConstant(constant1 == constant2 ? 1 : 0);
                case NE -> Value.makeConstant(constant1 != constant2 ? 1 : 0);
                case LT -> Value.makeConstant(constant1 < constant2 ? 1 : 0);
                case GT -> Value.makeConstant(constant1 > constant2 ? 1 : 0);
                case LE -> Value.makeConstant(constant1 <= constant2 ? 1 : 0);
                case GE -> Value.makeConstant(constant1 >= constant2 ? 1 : 0);
            };
        } else if (exp instanceof ShiftExp shiftExp) {
            return switch (shiftExp.getOperator()) {
                // I am so stupid that can't tell the difference between left and right, :(.
                // case SHR -> Value.makeConstant(constant1 << constant2);
                // case SHL -> Value.makeConstant(constant1 >> constant2);
                case SHL -> Value.makeConstant(constant1 << constant2);
                case SHR -> Value.makeConstant(constant1 >> constant2);
                case USHR -> Value.makeConstant(constant1 >>> constant2);
            };
        } else if (exp instanceof BitwiseExp bitwiseExp) {
            return switch (bitwiseExp.getOperator()) {
                case OR -> Value.makeConstant(constant1 | constant2);
                case AND -> Value.makeConstant(constant1 & constant2);
                case XOR -> Value.makeConstant(constant1 ^ constant2);
            };
        } else {
            return Value.getNAC();
        }
    }
}
