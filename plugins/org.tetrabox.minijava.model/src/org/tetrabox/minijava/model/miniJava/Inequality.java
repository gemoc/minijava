/**
 */
package org.tetrabox.minijava.model.miniJava;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Inequality</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.Inequality#getLeft <em>Left</em>}</li>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.Inequality#getRight <em>Right</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getInequality()
 * @model
 * @generated
 */
public interface Inequality extends Expression {
	/**
	 * Returns the value of the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Left</em>' containment reference.
	 * @see #setLeft(Expression)
	 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getInequality_Left()
	 * @model containment="true"
	 * @generated
	 */
	Expression getLeft();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.Inequality#getLeft <em>Left</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Left</em>' containment reference.
	 * @see #getLeft()
	 * @generated
	 */
	void setLeft(Expression value);

	/**
	 * Returns the value of the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Right</em>' containment reference.
	 * @see #setRight(Expression)
	 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage#getInequality_Right()
	 * @model containment="true"
	 * @generated
	 */
	Expression getRight();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.model.miniJava.Inequality#getRight <em>Right</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Right</em>' containment reference.
	 * @see #getRight()
	 * @generated
	 */
	void setRight(Expression value);

} // Inequality
