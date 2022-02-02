package org.tetrabox.minijava.semantics.tests.util

import java.util.List
import java.util.Map
import org.eclipse.xtend.lib.annotations.Data
import org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue
import org.tetrabox.minijava.model.miniJava.semantics.BooleanValue
import org.tetrabox.minijava.model.miniJava.semantics.IntegerValue
import org.tetrabox.minijava.model.miniJava.semantics.NullValue
import org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue
import org.tetrabox.minijava.model.miniJava.semantics.StringValue
import org.tetrabox.minijava.model.miniJava.semantics.Value

/**
 * TODO work in progress
 */
class MiniJavaValueEquals {

	@Data
	static class ObjectTemplate {
		val String typeName
		val Map<String, Object> bindings
	}

	@Data
	static class ArrayTemplate {
		val int size
		val String typeName
		val List<Object> content
	}

	def dispatch static boolean equals(Value v1, Object v2) {
		throw new UnsupportedOperationException();
	}

	def dispatch static boolean equals(IntegerValue v1, Integer v2) {
		return v1.value === v2
	}

	def dispatch static boolean equals(BooleanValue v1, Boolean v2) {
		return v1.value === v2
	}

	def dispatch static boolean equals(StringValue v1, String v2) {
		return v1.value == v2
	}

	def dispatch static boolean equals(ObjectRefValue v1, ObjectTemplate pattern) {

		if (v1.instance.type.name != pattern.typeName)
			return false;

		for (String fieldName : pattern.bindings.keySet) {
			val Object expectedValue = pattern.bindings.get(fieldName)
			val Value currentValue = v1.instance.fieldbindings.findFirst[it.field.name == fieldName].value
			if (! MiniJavaValueEquals::equals(currentValue, expectedValue))
				return false
		}
		return true;
	}

	def dispatch static boolean equals(NullValue v1, NullValue v2) {
		return true;
	}

	def dispatch static boolean equals(ArrayRefValue v1, ArrayTemplate v2) {
		if (v1.instance.size !== v2.size) {
			return false
		}

		for (v : v1.instance.value) {
			if (! MiniJavaValueEquals::equals(v, v2.getContent.get(v1.instance.value.indexOf(v))))
				return false
		} 

		return true
	}
}