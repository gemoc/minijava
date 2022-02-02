/**
 */
package org.tetrabox.minijava.model.miniJava.semantics;

import org.eclipse.emf.ecore.EObject;

import org.tetrabox.minijava.model.miniJava.Field;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Field Binding</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getField <em>Field</em>}</li>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getValue <em>Value</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getFieldBinding()
 * @model annotation="aspect"
 * @generated
 */
public interface FieldBinding extends EObject {
	/**
	 * Returns the value of the '<em><b>Field</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Field</em>' reference.
	 * @see #setField(Field)
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getFieldBinding_Field()
	 * @model required="true"
	 * @generated
	 */
	Field getField();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getField <em>Field</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Field</em>' reference.
	 * @see #getField()
	 * @generated
	 */
	void setField(Field value);

	/**
	 * Returns the value of the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Value</em>' containment reference.
	 * @see #setValue(Value)
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage#getFieldBinding_Value()
	 * @model containment="true"
	 * @generated
	 */
	Value getValue();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getValue <em>Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Value</em>' containment reference.
	 * @see #getValue()
	 * @generated
	 */
	void setValue(Value value);

} // FieldBinding
