package miniscala

import scala.collection.mutable
import scala.io.StdIn

object AbstractMachine {

  case class Executable(freevars: List[String], code: List[Instruction])

  sealed abstract class Instruction
  case class Const(c: Int) extends Instruction
  case object Add extends Instruction
  case object Sub extends Instruction
  case object Mul extends Instruction
  case object Div extends Instruction
  case object Eq extends Instruction
  case object Lt extends Instruction
  case object Leq extends Instruction
  case object And extends Instruction
  case object Or extends Instruction
  case object Neg extends Instruction
  case object Not extends Instruction
  case class Branch(thencode: List[Instruction], elsecode: List[Instruction]) extends Instruction
  case object EnterScope extends Instruction
  case class ExitScope(num: Int) extends Instruction
  case class Read(index: IdIndex) extends Instruction

  type IdIndex = Int // index of identifier in envstack

  def execute(program: Executable, initialEnv: List[Int]): Int = {

    var code: List[Instruction] = program.code // the program code to be executed
    val opstack = new mutable.Stack[Int] // operand stack, contains values of sub-expressions
    val envstack = new mutable.Stack[Int] // environment stack, contains values of identifiers

    for (c <- initialEnv)
      envstack.push(c)

    try {
      while (code.nonEmpty) {
        val inst = code.head
        code = code.tail
        trace(s"Current operand stack:     ${opstack.mkString("[", ", ", "]")}")
        trace(s"Current environment stack: ${envstack.mkString("[", ", ", "]")}")
        trace(s"Next instruction:          $inst")
        inst match {
          case Const(c) =>
            opstack.push(c)
          case Add =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            opstack.push(c1 + c2)
          case Sub =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            opstack.push(c1 - c2)
          case Mul =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            opstack.push(c1 * c2)
          case Div =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            opstack.push(c1 / c2)
          case Eq =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            if(c1 == c2) opstack.push(1) else opstack.push(0)
          case Lt =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            if (c1 < c2) opstack.push(1) else opstack.push(0)
          case Leq =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            if (c1 <= c2) opstack.push(1) else opstack.push(0)
          case And =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            if (c1 == 1 && c2 == 1) opstack.push(1) else opstack.push(0)
          case Or =>
            val c2 = opstack.pop()
            val c1 = opstack.pop()
            if (c1 == 1 || c2 == 1) opstack.push(1) else opstack.push(0)
          case Neg =>
            val c = opstack.pop()
            opstack.push(-c)
          case Not =>
            val c = opstack.pop()
            if (c == 0) opstack.push(1) else opstack.push(0)
          case Branch(thencode, elsecode) =>
            if (opstack.pop() == 1)
              code = thencode ++ code
            else
              code = elsecode ++ code
          case EnterScope =>
            val c = opstack.pop()
            envstack.push(c)
          case ExitScope(num) =>
            for (_ <- 1 to num)
              envstack.pop()
          case Read(index) =>
            opstack.push(envstack(index))
        }
      }
      opstack.pop()
    } catch {
      case ex: Exception => throw AbstractMachineError(ex)
    }
  }

  def makeInitialEnv(program: Executable): List[Int] = {
    program.freevars.foldLeft(List[Int]())((env, x) => {
      print(s"Please provide an integer value for the variable $x: ")
      StdIn.readInt() :: env
    })
  }

  def trace(msg: => String): Unit = if (Options.trace) println(msg)

  class AbstractMachineError(ex: Exception) extends Exception(ex)
}
