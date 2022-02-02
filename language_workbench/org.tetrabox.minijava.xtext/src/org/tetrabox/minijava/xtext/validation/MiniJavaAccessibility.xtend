package org.tetrabox.minijava.xtext.validation

import com.google.inject.Inject
import org.eclipse.emf.ecore.EObject
import org.tetrabox.minijava.model.miniJava.AccessLevel
import org.tetrabox.minijava.model.miniJava.Member
import org.tetrabox.minijava.model.miniJava.Class
import org.tetrabox.minijava.xtext.typing.MiniJavaTypeConformance

import static extension org.eclipse.xtext.EcoreUtil2.*

class MiniJavaAccessibility {

	@Inject extension MiniJavaTypeConformance

	def isAccessibleFrom(Member member, EObject context) {
		val contextClass = context.getContainerOfType(Class)
		val memberClass = member.getContainerOfType(Class)
		switch (contextClass) {
			case contextClass === memberClass:
				true
			case contextClass.isSubclassOf(memberClass):
				member.access != AccessLevel.PRIVATE
			default:
				member.access == AccessLevel.PUBLIC
		}
	}
}
