package org.tetrabox.minijava.semantics

import fr.inria.diverse.k3.al.annotationprocessor.Aspect
import fr.inria.diverse.k3.al.annotationprocessor.Containment
import fr.inria.diverse.k3.al.annotationprocessor.InitializeModel
import fr.inria.diverse.k3.al.annotationprocessor.Main
import fr.inria.diverse.k3.al.annotationprocessor.Step
import java.util.List
import org.tetrabox.minijava.model.miniJava.ArrayTypeRef
import org.tetrabox.minijava.model.miniJava.Method
import org.tetrabox.minijava.model.miniJava.Program
import org.tetrabox.minijava.model.miniJava.StringTypeRef
import org.tetrabox.minijava.model.miniJava.semantics.SemanticsFactory
import org.tetrabox.minijava.model.miniJava.semantics.State

import static extension org.tetrabox.minijava.semantics.BlockAspect.*

@Aspect(className=Program)
class ProgramAspect {

	@Containment
	public State state

	@Main
	@Step
	def void main() {
		_self.execute
	}


	

	@InitializeModel
	def void initialize(List<String> args) {
		val main = _self.classes.map[members].flatten.filter(Method).findFirst [
			it.name == "main" && it.static && it.params.size == 1 && it.params.head.typeRef instanceof ArrayTypeRef &&
				(it.params.head.typeRef as ArrayTypeRef).typeRef instanceof StringTypeRef
		]

		if (main !== null) {

			// Prepare args array
			val argsArray = SemanticsFactory::eINSTANCE.createArrayInstance
			argsArray.size = args.size
			for (arg : args) {
				val stringVal = SemanticsFactory::eINSTANCE.createStringValue => [value = arg]
				argsArray.value.add(stringVal)
			}

			// Prepare binding for args param
			val argsBinding = SemanticsFactory::eINSTANCE.createSymbolBinding => [
				symbol = main.params.head
				value = SemanticsFactory::eINSTANCE.createArrayRefValue => [
					instance = argsArray
				]
			]

			// Prepare root context with args binding
			val rootCont = SemanticsFactory::eINSTANCE.createContext
			rootCont.bindings.add(argsBinding)

			// Prepare initial state
			 
			val state = SemanticsFactory::eINSTANCE.createState => [
				outputStream = SemanticsFactory::eINSTANCE.createOutputStream
				rootFrame = SemanticsFactory::eINSTANCE.createFrame => [
					rootContext = rootCont
				]
			]
			state.arraysHeap.add(argsArray)
			_self.state = state

		} else
			throw new RuntimeException("No main method found.")
	}

	def State execute() {
		
		val main = _self.classes.map[members].flatten.filter(Method).findFirst [
			it.name == "main" && it.static && it.params.size == 1 && it.params.head.typeRef instanceof ArrayTypeRef &&
				(it.params.head.typeRef as ArrayTypeRef).typeRef instanceof StringTypeRef
		]
		// Start the main method
		main.body.evaluateStatementKeepContext(_self.state)
		return _self.state
	}

}
