package miniscala

import miniscala.Ast.*
import miniscala.Unparser.unparse

import scala.util.parsing.input.Position

/**
  * Type checker for MiniScala.
  */
object TypeChecker {

  type TypeEnv = Map[Id, Type]

  type ClassTypeEnv = Map[Id, StaticClassType]

  case class MutableType(thetype: Type) extends Type

  case class StaticClassType(srcpos: Position, params: List[FunParam], membertypes: TypeEnv, ctenv: ClassTypeEnv) extends Type

  val unitType: Type = TupleType(Nil)

  def typeCheck(e: Exp, tenv: TypeEnv, ctenv: ClassTypeEnv): Type = e match {
    case IntLit(_) => IntType()
    case BoolLit(_) => BoolType()
    case FloatLit(_) => FloatType()
    case StringLit(_) => StringType()
    case NullLit() => NullType()
    case VarExp(x) => tenv.getOrElse(x, throw TypeError(s"Unknown identifier '$x'", e)) match {
      case MutableType(thetype) => thetype
      case t: Type => t
    }
    case BinOpExp(leftexp, op, rightexp) =>
      val lefttype = typeCheck(leftexp, tenv, ctenv)
      val righttype = typeCheck(rightexp, tenv, ctenv)
      op match {
        case PlusBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) => IntType()
            case (FloatType(), FloatType()) => FloatType()
            case (IntType(), FloatType()) => FloatType()
            case (FloatType(), IntType()) => FloatType()
            case (StringType(), StringType()) => StringType()
            case (StringType(), IntType()) => StringType()
            case (StringType(), FloatType()) => StringType()
            case (IntType(), StringType()) => StringType()
            case (FloatType(), StringType()) => StringType()
            case _ => throw TypeError(s"Type mismatch at '+', unexpected types ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
        case MinusBinOp() | MultBinOp() | DivBinOp() | ModuloBinOp() | MaxBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) => IntType()
            case (FloatType(), FloatType()) => FloatType()
            case (FloatType(), IntType()) => FloatType()
            case (IntType(), FloatType()) => FloatType()
            case _ => throw TypeError(s"Type mismatch at '-', '*', '/', '%' or 'max' , unexpected types ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
        case EqualBinOp() => BoolType()
        case LessThanBinOp() | LessThanOrEqualBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) | (FloatType(), FloatType()) => BoolType()
            case (IntType(), FloatType()) | (FloatType(), IntType()) => BoolType()
            case _ => throw TypeError(s"Type mismatch at '<' or '<=', unexpected values ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
        case AndBinOp() | OrBinOp() =>
          (lefttype, righttype) match {
            case (BoolType(), BoolType()) => BoolType()
            case _ => throw TypeError(s"Type mismatch at '&' or '|', unexpected values ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
      }
    case UnOpExp(op, exp) =>
      val newExp = typeCheck(exp, tenv, ctenv)
      op match {
        case NegUnOp() =>
          newExp match {
            case IntType() => IntType()
            case FloatType() => FloatType()
          }
        case NotUnOp() =>
          newExp match {
            case BoolType() => BoolType()
          }
      }
    case IfThenElseExp(condexp, thenexp, elseexp) =>
      val condexptype = typeCheck(condexp, tenv, ctenv)
      val thenexptype = typeCheck(thenexp, tenv, ctenv)
      val elseexptype = typeCheck(elseexp, tenv, ctenv)
      condexptype match {
        case BoolType() =>
          (thenexptype, elseexptype) match {
            case (BoolType(), BoolType()) => BoolType()
            case (StringType(), StringType()) => StringType()
            case (IntType(), IntType()) => IntType()
            case (FloatType(), FloatType()) => FloatType()
            case _ => throw TypeError(s"Type mismatch at if statement, unexpected values ${unparse(thenexptype)} and ${unparse(elseexptype)}", IfThenElseExp(condexp, thenexp, elseexp))
          }
        case _ => throw TypeError(s"Type mismatch at if statement, unexpected value ${unparse(condexptype)}", IfThenElseExp(condexp, thenexp, elseexp))
      }
    case BlockExp(vals, vars, defs, classes, exps) =>
      var tenv1 = tenv
      var ctenv1 = ctenv
      for (d <- vals) {
        val d1 = ValDecl(d.x, getType(d.opttype, ctenv1), d.exp)
        val t = typeCheck(d1.exp, tenv1, ctenv)
        //val ot = getType(d.opttype, ctenv)
        val ot = d1.opttype
        checkSubtype(t, ot, d1)
        tenv1 = tenv1 + (d1.x -> ot.getOrElse(t))
      }
      for (d <- vars) {
        val d1 = VarDecl(d.x, getType(d.opttype, ctenv1), d.exp)
        val t = typeCheck(d1.exp, tenv1, ctenv)
        //val ot = getType(d.opttype, ctenv)
        val ot = d1.opttype
        checkSubtype(t, ot, d1)
        tenv1 = tenv1 + (d.x -> MutableType(d1.opttype.getOrElse(t)))
      }
      for (d <- defs) {
        val d1 = DefDecl(d.fun, d.params.map(f => FunParam(f.x, getType(f.opttype, ctenv1))), getType(d.optrestype, ctenv1), d.body)
        val tmpTenv = tenv1 ++ d1.params.map(f => f.x -> f.opttype.getOrElse(throw TypeError("Type not given", e))).toMap
        val t = typeCheck(d1.body, tmpTenv, ctenv)
        //val ot = getType(d.optrestype, ctenv)
        val ot = d1.optrestype
        checkSubtype(t, ot, d1)
        tenv1 = tenv1 + (d1.fun -> makeFunType(d1))
      }
      for (d <- classes) {
        val d1 = ClassDecl(d.klass, d.params.map(f => FunParam(f.x, getType(f.opttype, ctenv1))), d.body)
        val s @ StaticClassType(_, _, _, _) = makeStaticClassType(d1, ctenv1, classes)
        ctenv1 = ctenv1 + (d1.klass -> s)
      }
      for (d <- classes) { //Still need mutual recursion :(
        val StaticClassType(_, cParams, _, _) = ctenv1(d.klass)
        val tmpTenv = tenv1 ++ cParams.map(f => f.x -> f.opttype.getOrElse(throw TypeError("Type not given", e))).toMap
        typeCheck(d.body, tmpTenv, ctenv1)
      }
      var resultType: Type = unitType
      for (exp <- exps) {
        resultType = typeCheck(exp, tenv1, ctenv1)
      }
      resultType
    case TupleExp(exps) => TupleType(exps.map(x => typeCheck(x, tenv, ctenv)))
    case MatchExp(exp, cases) =>
      val exptype = typeCheck(exp, tenv, ctenv)
      exptype match {
        case TupleType(ts) =>
          for (c <- cases) {
            if (ts.length == c.pattern.length) {
              return typeCheck(c._2, tenv ++ c._1.zip(ts), ctenv)
            }
          }
          throw TypeError(s"No case matches type ${unparse(exptype)}", e)
        case _ => throw TypeError(s"Tuple expected at match, found ${unparse(exptype)}", e)
      }
    case CallExp(funexp, args) =>
      val FunType(paramtypes, restype) = typeCheck(funexp, tenv, ctenv)
      val varTypes = paramtypes
      val argTypes = args.map(x => typeCheck(x, tenv, ctenv))
      val varWithArgTypes = varTypes.zip(argTypes)

      if (argTypes.length != varTypes.length)
        throw TypeError(s"Number of argument types do not match", e)
      varWithArgTypes.foreach(t => checkSubtype(t._1, Option(t._2), e))

      restype
    case LambdaExp(params, body) =>
      val tmpTenv = tenv ++ params.map(p => (p._1 -> p._2.getOrElse(throw TypeError("Type not given", e)))).toMap
      typeCheck(body, tmpTenv, ctenv)
    case AssignmentExp(x, exp) =>
      val MutableType(oldType) = tenv(x)
      val newType = typeCheck(exp, tenv, ctenv)
      checkSubtype(newType, Option(oldType), e)
      unitType
    case WhileExp(cond, body) =>
      val condType = typeCheck(cond, tenv, ctenv)
      checkSubtype(condType, Option(BoolType()), e)
      unitType
    case NewObjExp(klass, args) => ctenv.getOrElse(klass, throw TypeError("Could not find "+klass+" in cenv", e)) match {
      case s @ StaticClassType(srcpos, params, membertypes, ctenv1) =>
        if (!(args.length == params.length)) throw TypeError("To many arguments uwu", e)

        val ctenv2 = ctenv1 + (klass -> s)
        val ParamTypes = params.map(f => f.opttype.getOrElse(throw TypeError(s"Type annotation missing at parameter ${f.x}", e)))
        args.zip(ParamTypes).foreach(x => checkSubtype(typeCheck(x._1, tenv, ctenv), Option(x._2), e))
        s
      case _ => throw TypeError("Did not find a StaticClassType, found: "+e.toString, e)
    }

    case LookupExp(objexp, member) => typeCheck(objexp, tenv, ctenv) match {
      case StaticClassType(srcpos, params, membertypes, ctenv1) => membertypes.getOrElse(member, throw TypeError("Could not find \""+member+"\" in membertypes", e))
      case _ => throw TypeError("Not a StaticClassType", e)
    }
  }

  /**
   * Checks whether `t1` is a subtype of `t2`.
   */
  def subtype(t1: Type, t2: Type): Boolean = {
    if (t1 == t2) true else (t1, t2) match {
      case (IntType(), FloatType()) => true
      case (NullType(), _) => true
      case (TupleType(list1), TupleType(list2)) =>
        for (tt <- list1.zip(list2)) {
          if (!subtype(tt._1, tt._2)) return false
        }
        true
      case (FunType(argTypes1, resultType1), FunType(argTypes2, resultType2)) =>
        subtype(TupleType(argTypes2), TupleType(argTypes1)) && subtype(resultType1, resultType2)
      case _ => false
    }
  }

  /**
   * Checks whether `t1` is a subtype of `t2`, generates type error otherwise.
   */
  def checkSubtype(t1: Type, t2: Type, n: AstNode): Unit =
    if (!subtype(t1, t2)) throw new TypeError(s"Type mismatch: type ${unparse(t1)} is not subtype of ${unparse(t2)}", n)

  /**
   * Checks whether `t1` is a subtype of `ot2` (if present), generates type error otherwise.
   */
  def checkSubtype(t: Type, ot2: Option[Type], n: AstNode): Unit = ot2 match {
    case Some(t2) => checkSubtype(t, t2, n)
    case None => // do nothing
  }

  /**
    * Returns the type described by the type annotation `t`.
    * Class names are converted to proper types according to the class type environment `ctenv`.
    */
  def getType(t: Type, ctenv: ClassTypeEnv): Type = t match {
    case ClassNameType(klass) => ctenv.getOrElse(klass, throw TypeError(s"Unknown class '$klass'", t))
    case IntType() | BoolType() | FloatType() | StringType() | NullType() => t
    case TupleType(ts) => TupleType(ts.map(tt => getType(tt, ctenv)))
    case FunType(paramtypes, restype) => FunType(paramtypes.map(tt => getType(tt, ctenv)), getType(restype, ctenv))
    case _ => throw RuntimeException(s"Unexpected type $t") // this case is unreachable...
  }

  /**
    * Returns the type described by the optional type annotation `ot` (if present).
    */
  def getType(ot: Option[Type], ctenv: ClassTypeEnv): Option[Type] = ot.map(t => getType(t, ctenv))

  /**
    * Returns the function type for the function declaration `d`.
    */
  def makeFunType(d: DefDecl): FunType =
    FunType(d.params.map(p => p.opttype.getOrElse(throw TypeError(s"Type annotation missing at parameter ${p.x}", p))),
      d.optrestype.getOrElse(throw TypeError(s"Type annotation missing at function result ${d.fun}", d)))

  /**
    * Returns the class type for the class declaration `d`.
    */
  def makeStaticClassType(d: ClassDecl, ctenv: ClassTypeEnv, classes: List[ClassDecl]): StaticClassType = {
    var membertypes: TypeEnv = Map()
    for (m <- d.body.vals)
      membertypes = membertypes + (m.x -> getType(m.opttype.getOrElse(throw TypeError(s"Type annotation missing at field ${m.x}", m)), ctenv))
    for (m <- d.body.vars)
      membertypes = membertypes + (m.x -> getType(m.opttype.getOrElse(throw TypeError(s"Type annotation missing at field ${m.x}", m)), ctenv))
    for (m <- d.body.defs)
      membertypes = membertypes + (m.fun -> getType(makeFunType(m), ctenv))
    StaticClassType(d.pos, d.params, membertypes, ctenv)
  }

  /**
    * Checks that the types `t1` and `ot2` are equal (if present), throws type error exception otherwise.
    */
  def checkTypesEqual(t1: Type, ot2: Option[Type], n: AstNode): Unit = ot2 match {
    case Some(t2) =>
      if (t1 != t2)
        throw TypeError(s"Type mismatch: expected type ${unparse(t2)}, found type ${unparse(t1)}", n)
    case None => // do nothing
  }

  /**
    * Builds an initial type environment, with a type for each free variable in the program.
    */
  def makeInitialTypeEnv(program: Exp): TypeEnv = {
    var tenv: TypeEnv = Map()
    for (x <- Vars.freeVars(program))
      tenv = tenv + (x -> IntType())
    tenv
  }

  /**
    * Exception thrown in case of MiniScala type errors.
    */
  class TypeError(msg: String, node: AstNode) extends MiniScalaError(s"Type error: $msg", node.pos)
}
