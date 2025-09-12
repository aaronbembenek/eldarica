/**
 * Copyright (c) 2011-2025 Hossein Hojjat, Filip Konecny, Philipp Ruemmer.
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.viewer

import lazabs.types._
import lazabs.ast.ASTree._
import lazabs.horn.global._
import lazabs.horn.parser.HornReader

import ap.parser.SMTLineariser

object HornSMTPrinter {

  import SMTLineariser.quoteIdentifier

  def apply(system: Seq[HornClause]): String =
    "(set-info :origin \"Horn problem converted to SMT-LIB2 using Eldarica (https://github.com/uuverifiers/eldarica)\")\n" +
    "(set-logic HORN)\n" +
    system.map(Horn.getRelVarSignatures(_)).flatten.distinct
      .map(rv => "(declare-fun " + quoteIdentifier(rv._1) +
                 " " + rv._2.map(type2String).mkString("("," ",")") +
                 " Bool)").mkString("\n") + "\n" +
      system.map(print).mkString("\n") + "\n(check-sat)"

  /**
   * gets the alphabetic character corresponding to an int 
   */
  def getAlphabeticChar(i :Int): String = {
    val alpha = i / 26
    /*"?" +*/ ((i % 26 + 65).toChar + (if(alpha > 0) alpha.toString else "")).toString
  }
  
  def type2String(t: Type) : String = t match {
    case AdtType(s) => SMTLineariser.sort2SMTString(s)
    case BooleanType() => "Bool"
    case BVType(n) => "(_ BitVec " + n + ")"
    case ArrayType(index, obj) => "(Array " + type2String(index) + " " + type2String(obj) + ")"
    case HeapType(h) => SMTLineariser.sort2SMTString(h.HeapSort)
    case HeapAddressType(h) => SMTLineariser.sort2SMTString(h.AddressSort)
    case HeapAddressRangeType(h) => SMTLineariser.sort2SMTString(h.AddressRangeSort)
    case HeapAllocResType(h) => SMTLineariser.sort2SMTString(h.AllocResSort)
    case HeapBatchAllocResType(h) => SMTLineariser.sort2SMTString(h.BatchAllocResSort)
    case HeapAdtType(h, s) => SMTLineariser.sort2SMTString(s)
    case _ => "Int"
  }
  
  /**
   * printing a horn clause
   */
  def print(h: HornClause): String = printFull(h, false)
  def printFull(h: HornClause, asDefineFun : Boolean): String = {    
    var varMap = Map[String,(Int,Type)]().empty
    var curVarCounter = -1
    def getNewVarCounter: Int = {
      curVarCounter = curVarCounter + 1
      curVarCounter
    }

    def printHornLiteral(hl: HornLiteral, sb: StringBuilder): Unit = hl match {
        case Interp(v) => printExp(v)(List(), sb)
        case RelVar(varName, params) =>
          if (params.isEmpty)
            sb ++= quoteIdentifier(varName)
          else
            sb ++= "(" + quoteIdentifier(varName) + " " + params
              .map(printParameter)
              .mkString(" ") + ")"
    }

    def stringifyHornLiteral(hl: HornLiteral): String = {
      var sb = new StringBuilder()
      printHornLiteral(hl, sb)
      sb.toString()
    }

    def printParameter(p: Parameter): String = varMap.get(p.name) match {
      case Some(i) => getAlphabeticChar(i._1)
      case None => 
        val newIndex = getNewVarCounter
        varMap += (p.name -> (newIndex,p.typ))
        getAlphabeticChar(newIndex)
    }

    def printNum(num : BigInt) : String =
      if (num<0) {
        "(- "+(num.abs)+")"
      } else {
        num.toString
      }

    def printExp(
        e: Expression
    )(implicit vars: List[String], sb: StringBuilder): Unit = {

      def printOp(op: String, args: Expression*): Unit = {
        sb ++= "(" + op
        printExps(args)
        sb ++= ")"
      }

      def printExps(args: Seq[Expression]): Unit = {
        for (arg <- args) {
          sb ++= " "
          printExp(arg)
        }
      }

      e match {
        case Existential(v, qe) => {
          val name = "var" + vars.size
          sb ++= "(exists ((" + name + " " + type2String(v.stype) + ")) "
          printExp(qe)(name :: vars, sb)
          sb ++= ")"
        }
        case Universal(v, qe) => {
          val name = "var" + vars.size
          sb ++= "(forall ((" + name + " " + type2String(v.stype) + ")) "
          printExp(qe)(name :: vars, sb)
          sb ++= ")"
        }
        case Conjunction(e1, e2) => printOp("and", e1, e2)
        case Disjunction(e1, e2) => printOp("or", e1, e2)

        // special handling of the tester predicates of ADTs
        case e @ Equality(NumericalConst(num), ADTtest(adt, sortNum, expr)) => {
          sb ++= "(is-" + adt.getCtorPerSort(sortNum, num.toInt).name + " "
          printExp(expr)
          sb ++= ")"
        }
        case e @ Equality(ADTtest(adt, sortNum, expr), NumericalConst(num)) => {
          sb ++= "(is-" + adt.getCtorPerSort(sortNum, num.toInt).name + " "
          printExp(expr)
          sb ++= ")"
        }

        case Equality(e1, e2)         => printOp("=", e1, e2)
        case Inequality(e1, e2)       => printExp(Not(Equality(e1, e2)))
        case LessThan(e1, e2)         => printOp("<", e1, e2)
        case LessThanEqual(e1, e2)    => printOp("<=", e1, e2)
        case GreaterThan(e1, e2)      => printOp(">", e1, e2)
        case GreaterThanEqual(e1, e2) => printOp(">=", e1, e2)
        case Modulo(e1, e2)           => printOp("mod", e1, e2)
        case Addition(e1, e2)         => printOp("+", e1, e2)
        case Subtraction(e1, e2)      => printOp("-", e1, e2)
        case Multiplication(e1, e2)   => printOp("*", e1, e2)
        case Division(e1, e2)         => printOp("div", e1, e2)
        case ADTctor(adt, name, exprList) =>
          if (exprList.isEmpty)
            sb ++= quoteIdentifier(name)
          else {
            sb ++= "(" + quoteIdentifier(name)
            printExps(exprList)
            sb ++= ")"
          }
        case ADTsel(adt, name, exprList) =>
          sb ++= "(" + quoteIdentifier(name)
          printExps(exprList)
          sb ++= ")"
        case ADTsize(adt, _, v)          => printOp("_size", v)
        case ArraySelect(ar, ind)        => printOp("select", ar, ind)
        case ArrayUpdate(ar, ind, value) => printOp("store", ar, ind, value)
        case ConstArray(value) =>
          printOp("(as const " + type2String(e.stype) + ")", value)
        case HeapFun(heap, name, exprList) =>
          if (exprList.isEmpty)
            sb ++= quoteIdentifier(name)
          else {
            sb ++= "(" + quoteIdentifier(name)
            printExps(exprList)
            sb ++= ")"
          }
        case HeapPred(heap, name, exprList) => {
          sb ++= "(" + quoteIdentifier(name)
          printExps(exprList)
          sb ++= ")"
        }
        case Not(e)   => printOp("not", e)
        case Minus(e) => printOp("-", e)
        case v @ Variable(name, None) =>
          varMap.get(name) match {
            case Some(i) => sb ++= getAlphabeticChar(i._1)
            case None => {
              val newIndex = getNewVarCounter
              varMap += (name -> (newIndex, v.stype))
              sb ++= getAlphabeticChar(newIndex)
            }
          }
        case Variable(_, Some(index)) =>
          if (index < vars.size)
            sb ++= vars(index)
          else
            sb ++= getAlphabeticChar(index - vars.size)
        case NumericalConst(num) =>
          if (num < 0) {
            sb ++= "(- " + (num.abs) + ")"
          } else {
            sb ++= num.toString
          }
        case BoolConst(v) => sb ++= quoteIdentifier(v.toString)

        case BVconst(bits, v)    => sb ++= "(_ bv" + v + " " + bits + ")"
        case Int2BitVec(bits, e) => printOp("(_ int2bv " + bits + ")", e)
        case UnaryExpression(op: BVneg, e) => printOp(op.st, e)
        // Special printing for concat to make it easy to extract type information
        case BinaryExpression(e1, op: BVconcat, e2) => printOp("concat<" + op.bits1 + "," + op.bits2 + ">", e1, e2)
        case BinaryExpression(e1, op, e2) => printOp(op.st, e1, e2)

        case _ =>
          throw new Exception("Don't know how to print expression " + e)
      }
    }
    val head = stringifyHornLiteral(h.head)
    val body = h.body.size match {
      case 0 => ""
      case 1 => stringifyHornLiteral(h.body.head)
      case _ => {
        // print first the relation variables, then constraints
        val (relVars, other) = h.body partition (_.isInstanceOf[RelVar])
        var sb = new StringBuilder()
        sb ++= "(and"
        for (x <- (relVars ++ other)) {
          sb ++= " "
          printHornLiteral(x, sb)
        }
        sb ++= ")"
        sb.toString()
      }
    }
    
    if (asDefineFun) {
      val RelVar(name, params) = h.head

      val args = (for (p <- params) yield {
        val (ind, t) = varMap(p.name)
        "(" + getAlphabeticChar(ind) + " " +
          type2String(varMap(p.name)._2) + ")"
      }) mkString " "

      "(define-fun " + quoteIdentifier(name) +
      " (" + args + ") Bool " + body + ")"
    } else {
      val boundVars =
        varMap.values.toSeq.sortWith(_._1 < _._1)
              .map(v => "(" + getAlphabeticChar(v._1) + " " +
                        type2String(v._2) + ")")
              .mkString(" ")

      h.head match{
        case Interp(BoolConst(false)) =>
          if (boundVars.isEmpty) {
            "(assert (=> " + body + " false))"
          } else {
            "(assert (forall (" + boundVars + ") (=> " + body + " false)))"
          }
        case _ => 
          if (boundVars.isEmpty) {
            "(assert" + "(=> " + body + " " + head + "))"
          } else {
            "(assert (forall (" + boundVars + ") " +
            "(=> " + body + " " + head + ")))"
          }
      }
    }
  }
}
