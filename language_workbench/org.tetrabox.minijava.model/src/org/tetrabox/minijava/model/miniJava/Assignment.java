/**
 */
package org.tetrabox.minijava.model.miniJava;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Assignment</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.Assignment#getAssignee <em>Assignee</em>}</li>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.Assignment#getValue <em>Value</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getAssignment()
 * @model
 * @generated
 */
public interface Assignment extends Statement {
	/**
	 * Returns the value of the '<em><b>Assignee</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Assignee</em>' containment reference.
	 * @see #setAssignee(Assignee)
	 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getAssignment_Assignee()
	 * @model containment="true"
	 * @generated
	 */
	Assignee getAssignee();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.Assignment#getAssignee <em>Assignee</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Assignee</em>' containment reference.
	 * @see #getAssignee()
	 * @generated
	 */
	void setAssignee(Assignee value);

	/**
	 * Returns the value of the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Value</em>' containment reference.
	 * @see #setValue(Expression)
	 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getAssignment_Value()
	 * @model containment="true"
	 * @generated
	 */
	Expression getValue();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.Assignment#getValue <em>Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Value</em>' containment reference.
	 * @see #getValue()
	 * @generated
	 */
	void setValue(Expression value);

} // Assignment
