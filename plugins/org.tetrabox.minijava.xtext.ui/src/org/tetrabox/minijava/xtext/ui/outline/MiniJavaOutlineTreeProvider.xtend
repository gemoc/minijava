/*
 * generated by Xtext 2.10.0
 */
package org.tetrabox.minijava.xtext.ui.outline

import org.eclipse.xtext.ui.editor.outline.impl.DefaultOutlineTreeProvider
import org.eclipse.xtext.ui.editor.outline.impl.DocumentRootNode
import org.tetrabox.minijava.model.miniJava.Method
import org.tetrabox.minijava.model.miniJava.Program

/**
 * Customization of the default outline structure.
 * 
 * See https://www.eclipse.org/Xtext/documentation/304_ide_concepts.html#outline
 */
class MiniJavaOutlineTreeProvider extends DefaultOutlineTreeProvider {
	def _isLeaf(Method m) {
		true
	}

	def void _createChildren(DocumentRootNode outlineNode, Program model) {
		model.classes.forEach [ cl |
			createNode(outlineNode, cl);
		]
	}
}