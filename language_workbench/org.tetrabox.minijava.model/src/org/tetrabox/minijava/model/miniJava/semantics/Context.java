/**
 */
package org.tetrabox.minijava.model.miniJava.semantics;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Context</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getBindings <em>Bindings</em>}</li>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getParentContext <em>Parent Context</em>}</li>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getChildContext <em>Child Context</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getContext()
 * @model annotation="aspect"
 * @generated
 */
public interface Context extends EObject {
	/**
	 * Returns the value of the '<em><b>Bindings</b></em>' containment reference list.
	 * The list contents are of type {@link org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Bindings</em>' containment reference list.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getContext_Bindings()
	 * @model containment="true"
	 * @generated
	 */
	EList<SymbolBinding> getBindings();

	/**
	 * Returns the value of the '<em><b>Parent Context</b></em>' container reference.
	 * It is bidirectional and its opposite is '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getChildContext <em>Child Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parent Context</em>' container reference.
	 * @see #setParentContext(Context)
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getContext_ParentContext()
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Context#getChildContext
	 * @model opposite="childContext" transient="false"
	 * @generated
	 */
	Context getParentContext();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getParentContext <em>Parent Context</em>}' container reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Parent Context</em>' container reference.
	 * @see #getParentContext()
	 * @generated
	 */
	void setParentContext(Context value);

	/**
	 * Returns the value of the '<em><b>Child Context</b></em>' containment reference.
	 * It is bidirectional and its opposite is '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getParentContext <em>Parent Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Child Context</em>' containment reference.
	 * @see #setChildContext(Context)
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getContext_ChildContext()
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Context#getParentContext
	 * @model opposite="parentContext" containment="true"
	 * @generated
	 */
	Context getChildContext();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getChildContext <em>Child Context</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Child Context</em>' containment reference.
	 * @see #getChildContext()
	 * @generated
	 */
	void setChildContext(Context value);

} // Context
