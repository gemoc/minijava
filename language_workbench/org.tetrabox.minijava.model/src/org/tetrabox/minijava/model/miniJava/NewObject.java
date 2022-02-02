/**
 */
package org.tetrabox.minijava.model.miniJava;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>New Object</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.NewObject#getType <em>Type</em>}</li>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.NewObject#getArgs <em>Args</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getNewObject()
 * @model
 * @generated
 */
public interface NewObject extends Expression {
	/**
	 * Returns the value of the '<em><b>Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Type</em>' reference.
	 * @see #setType(org.tetrabox.minijava.model.miniJava.Class)
	 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getNewObject_Type()
	 * @model
	 * @generated
	 */
	org.tetrabox.minijava.model.miniJava.Class getType();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.NewObject#getType <em>Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Type</em>' reference.
	 * @see #getType()
	 * @generated
	 */
	void setType(org.tetrabox.minijava.model.miniJava.Class value);

	/**
	 * Returns the value of the '<em><b>Args</b></em>' containment reference list.
	 * The list contents are of type {@link org.tetrabox.minijava.model.miniJava.Expression}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Args</em>' containment reference list.
	 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getNewObject_Args()
	 * @model containment="true"
	 * @generated
	 */
	EList<Expression> getArgs();

} // NewObject
