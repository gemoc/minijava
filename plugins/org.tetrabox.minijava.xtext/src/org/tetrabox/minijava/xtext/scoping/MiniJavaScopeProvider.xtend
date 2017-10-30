/*
 * generated by Xtext 2.10.0
 */
package org.tetrabox.minijava.xtext.scoping

import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.EReference
import org.eclipse.xtext.scoping.IScope
import org.eclipse.xtext.scoping.Scopes
import org.tetrabox.minijava.xtext.miniJava.Block
import org.tetrabox.minijava.xtext.miniJava.Method
import org.tetrabox.minijava.xtext.miniJava.VariableDeclaration
import org.tetrabox.minijava.xtext.miniJava.MiniJavaPackage
import org.tetrabox.minijava.xtext.miniJava.MemberSelection
import com.google.inject.Inject
import org.tetrabox.minijava.xtext.MiniJavaModelUtil
import org.tetrabox.minijava.xtext.typing.MiniJavaTypeComputer

/**
 * This class contains custom scoping description.
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#scoping
 * on how and when to use it.
 */
class MiniJavaScopeProvider extends AbstractMiniJavaScopeProvider {

	val epackage = MiniJavaPackage.eINSTANCE
	@Inject extension MiniJavaModelUtil
	@Inject extension MiniJavaTypeComputer

	override getScope(EObject context, EReference reference) {
		if (reference == epackage.symbolRef_Variable) {
			return scopeForSymbolRef(context)
		} else if (context instanceof MemberSelection) {
			return scopeForMemberSelection(context)
		}
		return super.getScope(context, reference)
	}

	def protected IScope scopeForSymbolRef(EObject context) {
		val container = context.eContainer
		return switch (container) {
			Method:
				Scopes.scopeFor(container.params)
			Block:
				Scopes.scopeFor(
					container.statements.takeWhile[it != context].filter(VariableDeclaration),
					scopeForSymbolRef(container) // outer scope
				)
			default:
				scopeForSymbolRef(container)
		}
	}

	def protected IScope scopeForMemberSelection(MemberSelection sel) {
		val type = sel.receiver.typeFor

		if (type === null || type.isPrimitive)
			return IScope.NULLSCOPE

		val grouped = type.
			classHierarchyMembers.groupBy[it instanceof Method]
		val inheritedMethods = grouped.get(true) ?: emptyList
		val inheritedFields = grouped.get(false) ?: emptyList

		if (sel.methodinvocation) {
			return Scopes.scopeFor(
				type.methods + type.fields,
				Scopes.scopeFor(inheritedMethods + inheritedFields)
			)
		} else {
			return Scopes.scopeFor(
				type.fields + type.methods,
				Scopes.scopeFor(inheritedFields + inheritedMethods)
			)
		}
	}

}
