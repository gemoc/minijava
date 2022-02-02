package org.tetrabox.minijava.xtext.typing

import org.tetrabox.minijava.model.miniJava.Assignment
import org.tetrabox.minijava.model.miniJava.BoolConstant
import org.tetrabox.minijava.model.miniJava.BooleanTypeRef
import org.tetrabox.minijava.model.miniJava.ClassRef
import org.tetrabox.minijava.model.miniJava.Expression
import org.tetrabox.minijava.model.miniJava.FieldAccess
import org.tetrabox.minijava.model.miniJava.IntConstant
import org.tetrabox.minijava.model.miniJava.IntegerTypeRef
import org.tetrabox.minijava.model.miniJava.Method
import org.tetrabox.minijava.model.miniJava.MethodCall
import org.tetrabox.minijava.model.miniJava.MiniJavaFactory
import org.tetrabox.minijava.model.miniJava.MiniJavaPackage
import org.tetrabox.minijava.model.miniJava.NewObject
import org.tetrabox.minijava.model.miniJava.Null
import org.tetrabox.minijava.model.miniJava.Class
import org.tetrabox.minijava.model.miniJava.Return
import org.tetrabox.minijava.model.miniJava.StringConstant
import org.tetrabox.minijava.model.miniJava.StringTypeRef
import org.tetrabox.minijava.model.miniJava.Super
import org.tetrabox.minijava.model.miniJava.SymbolRef
import org.tetrabox.minijava.model.miniJava.This
import org.tetrabox.minijava.model.miniJava.TypeDeclaration
import org.tetrabox.minijava.model.miniJava.TypeRef
import org.tetrabox.minijava.model.miniJava.VariableDeclaration
import org.tetrabox.minijava.model.miniJava.VoidTypeRef
import static org.eclipse.xtext.EcoreUtil2.getContainerOfType
import org.eclipse.xtext.EcoreUtil2

class MiniJavaTypeComputer {
	private static val factory = MiniJavaFactory.eINSTANCE
	public static val STRING_TYPE = factory.createClass => [name = 'stringType']
	public static val INT_TYPE = factory.createClass => [name = 'intType']
	public static val BOOLEAN_TYPE = factory.createClass => [name = 'booleanType']
	public static val NULL_TYPE = factory.createClass => [name = 'nullType']

	static val ep = MiniJavaPackage.eINSTANCE

	def TypeDeclaration getType(TypeRef r) {
		switch r {
			ClassRef: r.referencedClass
			IntegerTypeRef: INT_TYPE
			BooleanTypeRef: BOOLEAN_TYPE
			StringTypeRef: STRING_TYPE
			VoidTypeRef : NULL_TYPE
		}
	}

	def TypeDeclaration typeFor(Expression e) {
		switch (e) {
			SymbolRef:
				e.symbol.typeRef.type
			FieldAccess:
				e.field.typeRef.type
			MethodCall:
				e.method.typeRef.type
			NewObject:
				e.type
			This:
				EcoreUtil2.getContainerOfType(e, Class)
			Super:
				EcoreUtil2.getContainerOfType(e, Class).superClass
			Null:
				NULL_TYPE
			StringConstant:
				STRING_TYPE
			IntConstant:
				INT_TYPE
			BoolConstant:
				BOOLEAN_TYPE
		}
	}


	def isPrimitive(TypeDeclaration c) {
		c.eResource === null
	}

	def TypeDeclaration expectedType(Expression e) {
		val c = e.eContainer
		val f = e.eContainingFeature
		switch (c) {
			VariableDeclaration:
				c.typeRef.type
			Assignment case f == ep.assignment_Value: {
				val assignee = c.assignee
				switch (assignee) {
					VariableDeclaration: assignee.typeRef.type
					FieldAccess: assignee.typeFor
				}
			}
			Return:
				EcoreUtil2.getContainerOfType(c, Method).typeRef.type
			case f == ep.ifStatement_Expression:
				BOOLEAN_TYPE
			MethodCall case f == ep.methodCall_Args: {
				if (c.method !== null) {
				if (c.method.params.size > c.args.indexOf(e))
					c.method.params.get(c.args.indexOf(e)).typeRef.type
				}
			}
			NewObject case f == ep.newObject_Args: {
				c.type.members.filter(Method).findFirst[it.name === null && it.params.size === c.args.size].params.get(c.args.indexOf(e)).typeRef.type
			}
		}
	}
}
