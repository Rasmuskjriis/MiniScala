package miniscala

import miniscala.Ast.{MinusBinOp, *}

/**
  * Unparser for MiniScala.
  */
object Unparser {

  // this unparse function can be used for all kinds of AstNode objects, including Exp objects (see Ast.scala)
  def unparse(n: AstNode): String = n match {
    case IntLit(c) => "" + c
    case BoolLit(c) => if (c) "true" else "false"
    case FloatLit(c) => "" + c
    case StringLit(c) => "\"" + c + "\""
    case VarExp(x) => x
    case BinOpExp(leftexp, op, rightexp) =>
      val leftString = unparse(leftexp)
      val rightString = unparse(rightexp)
      op match {
        case PlusBinOp() => "(" + leftString + "+" + rightString + ")"
        case MinusBinOp() => "(" + leftString + "-" + rightString + ")"
        case MultBinOp() => "(" + leftString + "*" + rightString + ")"
        case DivBinOp() => "(" + leftString + "/" + rightString + ")"
        case ModuloBinOp() => "(" + leftString + " mod " + rightString + ")"
        case MaxBinOp() => "max(" + leftString + ", " + rightString + ")"
        case EqualBinOp() => "("+leftString+"=="+rightString+")"
        case LessThanBinOp() => "("+leftString+"<"+rightString+")"
      }
    case UnOpExp(op, exp) =>
      val expString = unparse(exp)
      op match {
        case NegUnOp() => "(-" + expString + ")"
        case NotUnOp() => "(!"+expString+")"
      }
    case IfThenElseExp(condexp, thenexp, elseexp) =>
      "if (" + unparse(condexp) + ") " + unparse(thenexp) + " else " + unparse(elseexp)
    case BlockExp(valDecls, varDecls, defDecls, classDecl, exps) =>
      val declsAndExps = valDecls ++ varDecls ++ defDecls ++ classDecl ++ exps
      declsAndExps.map(unparse).mkString("{", "; ", "}")
    case TupleExp(exps) =>
      exps.map(x => unparse(x)).mkString("(", ",", ")")
    case ValDecl(name, varType, exp) => "val "+name+unparse(varType)+" = "+unparse(exp)
    case DefDecl(fun, params, optrestype, body) =>
      "def "+fun+params.map(unparse).mkString("(", ", ", ")")+unparse(optrestype)+" = "+unparse(body)
    case VarDecl(x, opttype, exp) => "var "+x+unparse(opttype)+" = "+unparse(exp)
    case ClassDecl(klass, params, body) =>
      "class "+klass+params.map(unparse).mkString("(", ", ", ")")+" = "+unparse(body)
    case AssignmentExp(x, exp) => x+" = "+unparse(exp)
    case MatchExp(exp, cases) =>
      unparse(exp) + cases.map(x => unparse(x)).mkString(" match { ", "; ", "}")
    case MatchCase(pattern, exp) => "case ("+pattern.mkString(", ")+") => "+unparse(exp)
    case CallExp(fun, args) => unparse(fun)+args.map(unparse).mkString("(",", ",")")
    case LambdaExp(x, body) => "("+x.map(unparse).mkString("(",", ", ")")+"=>"+unparse(body)+")"
    case FunParam(x, opttype) => x+unparse(opttype)
    case NewObjExp(klass, args) => "new "+klass+args.map(unparse).mkString("(",", ",")")
    case LookupExp(objexp, member) => unparse(objexp)+"."+member
    case _ => n.toString
  }

  def unparse(ot: Option[Type]): String = ot match {
    case Some(t) => ": " + unparse(t)
    case None => ""
  }
}
