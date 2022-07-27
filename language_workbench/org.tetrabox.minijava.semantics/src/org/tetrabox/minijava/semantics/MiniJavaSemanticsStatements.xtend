package org.tetrabox.minijava.semantics

import fr.inria.diverse.k3.al.annotationprocessor.Aspect
import fr.inria.diverse.k3.al.annotationprocessor.OverrideAspectMethod
import fr.inria.diverse.k3.al.annotationprocessor.Step
import org.tetrabox.minijava.model.miniJava.ArrayAccess
import org.tetrabox.minijava.model.miniJava.Assignment
import org.tetrabox.minijava.model.miniJava.Block
import org.tetrabox.minijava.model.miniJava.Expression
import org.tetrabox.minijava.model.miniJava.Field
import org.tetrabox.minijava.model.miniJava.FieldAccess
import org.tetrabox.minijava.model.miniJava.ForStatement
import org.tetrabox.minijava.model.miniJava.IfStatement
import org.tetrabox.minijava.model.miniJava.Method
import org.tetrabox.minijava.model.miniJava.PrintStatement
import org.tetrabox.minijava.model.miniJava.Return
import org.tetrabox.minijava.model.miniJava.Statement
import org.tetrabox.minijava.model.miniJava.SymbolRef
import org.tetrabox.minijava.model.miniJava.VariableDeclaration
import org.tetrabox.minijava.model.miniJava.WhileStatement
import org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue
import org.tetrabox.minijava.model.miniJava.semantics.BooleanValue
import org.tetrabox.minijava.model.miniJava.semantics.IntegerValue
import org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue
import org.tetrabox.minijava.model.miniJava.semantics.SemanticsFactory
import org.tetrabox.minijava.model.miniJava.semantics.State

import static extension org.tetrabox.minijava.semantics.BlockAspect.*
import static extension org.tetrabox.minijava.semantics.ContextAspect.*
import static extension org.tetrabox.minijava.semantics.ExpressionAspect.*
import static extension org.tetrabox.minijava.semantics.StateAspect.*
import static extension org.tetrabox.minijava.semantics.ValueToStringAspect.*
import org.tetrabox.minijava.model.miniJava.semantics.Value
import org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding
import org.tetrabox.minijava.model.miniJava.semantics.Context
import org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance
import org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance

@Aspect(className=Block)
class BlockAspect extends StatementAspect {

	def void evaluateStatementKeepContext(State state) {
		_self.doPushNextContext(state)
		val currentFrame = state.findCurrentFrame
		var i = _self.statements.iterator
		while (i.hasNext && currentFrame.returnValue === null) {
			i.next.evaluateStatement(state)
		}
	}

	@OverrideAspectMethod
	def void evaluateStatement(State state) {
		_self.evaluateStatementKeepContext(state)
		_self.doPopCurrentContext(state)
	}

	// Observe only
	@Step
	def void doPushNextContext(State state) {
		state.pushNewContext
	}

	// Observe only
	@Step
	def void doPopCurrentContext(State state) {
		state.popCurrentContext
	}

}

@Aspect(className=Statement)
class StatementAspect {
	@Step
	def void evaluateStatement(State state) {
		throw new RuntimeException('''evaluate should be overriden for type «_self.class.name»''')
	}
}

@Aspect(className=PrintStatement)
class PrintStatementAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		val printedValue = _self.evaluatePrintExpression(state)
		_self.doPrint(state, printedValue)
	}

	// Observe only
	@Step
	def String evaluatePrintExpression(State state) {
		return _self.expression.evaluateExpression(state).customToString
	}

	// Observe only
	@Step
	def void doPrint(State state, String printedValue) {
		state.println(printedValue)
	}

}

@Aspect(className=Assignment)
class AssigmentAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		val context = state.findCurrentContext
		val right = _self.evaluateValue(state)
		val assignee = _self.assignee
		switch (assignee) {
			SymbolRef: {
				val existingBinding = context.findBinding(assignee.symbol)
				_self.doAssignment(existingBinding, right)
			}
			VariableDeclaration: {
				val binding = SemanticsFactory::eINSTANCE.createSymbolBinding => [
					symbol = assignee
					value = right
				]
				_self.doAssignment(context, binding)
			}
			FieldAccess: {
				val f = assignee.field as Field
				val realReceiver = _self.evaluateAssignee(state, assignee)
				_self.doAssignment(realReceiver, f, right)
			}
			ArrayAccess: {
				val array = _self.evaluateArray(state, assignee)
				val index = _self.evaluateIndex(state, assignee)
				_self.doAssignment(array, index, right)

			}
			default:
				throw new Exception("Cannot assign a value to " + assignee)
		}
	}

	// Observe only
	@Step
	def Value evaluateValue(State state) {
		return _self.value.evaluateExpression(state)
	}

	// Observe only
	@Step
	def ObjectInstance evaluateAssignee(State state, FieldAccess assignee) {
		return (assignee.receiver.evaluateExpression(state) as ObjectRefValue).instance
	}

	// Observe only
	@Step
	def ArrayInstance evaluateArray(State state, ArrayAccess assignee) {
		return (assignee.object.evaluateExpression(state) as ArrayRefValue).instance
	}

	// Observe only
	@Step
	def int evaluateIndex(State state, ArrayAccess assignee) {
		return (assignee.index.evaluateExpression(state) as IntegerValue).value
	}

	// Observe only
	@Step
	def void doAssignment(SymbolBinding existingBinding, Value value) {
		existingBinding.value = value
	}

	// Observe only
	@Step
	def void doAssignment(Context context, SymbolBinding newBinding) {
		context.bindings.add(newBinding)
	}

	// Observe only
	@Step
	def void doAssignment(ObjectInstance receiver, Field changedField, Value newValue) {
		val existingBinding = receiver.fieldbindings.findFirst[it.field === changedField]
		if (existingBinding !== null) {
			existingBinding.value = newValue
		} else {
			val binding = SemanticsFactory::eINSTANCE.createFieldBinding => [
				field = changedField
				value = newValue
			]
			receiver.fieldbindings.add(binding)
		}
	}

	// Observe only
	@Step
	def void doAssignment(ArrayInstance array, int index, Value right) {
		array.value.set(index, right)
	}

}

@Aspect(className=ForStatement)
class ForStatementAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		_self.doPushNextContext(state)
		for (_self.declaration.evaluateStatement(state); _self.evaluateCondition(state); _self.
			progression.evaluateStatement(state)) {
			_self.block.evaluateStatement(state)
		}
		_self.doPopCurrentContext(state)
	}

	// Observe only
	@Step
	def void doPushNextContext(State state) {
		state.pushNewContext
	}

	// Observe only
	@Step
	def void doPopCurrentContext(State state) {
		state.popCurrentContext
	}

	// Observe only
	@Step
	def boolean evaluateCondition(State state) {
		return (_self.condition.evaluateExpression(state) as BooleanValue).value
	}

}

@Aspect(className=IfStatement)
class IfStatementAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		if (_self.evaluateCondition(state)) {
			_self.thenBlock.evaluateStatement(state)
		} else if (_self.elseBlock !== null) {
			_self.elseBlock.evaluateStatement(state)
		}
	}
	
	// Observe only
	@Step
	def boolean evaluateCondition(State state) {
		return (_self.expression.evaluateExpression(state) as BooleanValue).value
	}
}

@Aspect(className=WhileStatement)
class WhileStatementAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		while (_self.evaluateCondition(state)) { 
			_self.block.evaluateStatement(state)
		}
	}
	
	// Observe only
	@Step
	def boolean evaluateCondition(State state) {
		return (_self.condition.evaluateExpression(state) as BooleanValue).value
	}
}

@Aspect(className=Expression)
class ExpressionStatementAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		_self.evaluateExpression(state)
	}
}

@Aspect(className=Return)
class ReturnAspect extends StatementAspect {
	@OverrideAspectMethod
	@Step
	def void evaluateStatement(State state) {
		val value = _self.evaluateValue(state); 
		_self.doReturn(state, value)
	}
	
	// Observe only
	@Step
	def Value evaluateValue(State state) {
		return _self.expression.evaluateExpression(state);
	}
	
	// Observe only
	@Step
	def void doReturn(State state, Value value) {
		state.findCurrentFrame.returnValue = value 
	}
}

@Aspect(className=Method)
class MethodSortofStatementAspect {
	@Step
	def void call(State state) {
		_self.body.evaluateStatement(state)
	}
}
