package org.tetrabox.minijava.semantics

import fr.inria.diverse.k3.al.annotationprocessor.Aspect

import fr.inria.diverse.k3.al.annotationprocessor.OverrideAspectMethod
import org.tetrabox.minijava.model.miniJava.BooleanValue
import org.tetrabox.minijava.model.miniJava.IntegerValue
import org.tetrabox.minijava.model.miniJava.StringValue
import org.tetrabox.minijava.model.miniJava.Value
import org.tetrabox.minijava.model.miniJava.ObjectRefValue

@Aspect(className=Value)
class ValueToStringAspect {
	def String customToString() {}
}

@Aspect(className=ObjectRefValue)
class ObjectRefValueToStringAspect extends ValueToStringAspect {
	@OverrideAspectMethod
	def String customToString() {
		return '''«_self.instance.type.name» {«FOR b : _self.instance.fieldbindings SEPARATOR "\n\t"»«b.field.name»: «b.value.customToString »«ENDFOR»}''';
	}
}

@Aspect(className=IntegerValue)
class IntegerValueToStringAspect extends ValueToStringAspect {
	@OverrideAspectMethod
	def String customToString() {
		return _self.value.toString
	}
}

@Aspect(className=BooleanValue)
class BooleanValueToStringAspect extends ValueToStringAspect {
	@OverrideAspectMethod
	def String customToString() {
		return _self.value.toString
	}
}

@Aspect(className=StringValue)
class StringValueToStringAspect extends ValueToStringAspect {
	@OverrideAspectMethod
	def String customToString() {
		return _self.value.toString
	}
}
