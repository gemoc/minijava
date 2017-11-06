/**
 */
package org.tetrabox.minijava.xminijavamt.miniJava;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Method Call</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.xminijavamt.miniJava.MethodCall#getReceiver <em>Receiver</em>}</li>
 *   <li>{@link org.tetrabox.minijava.xminijavamt.miniJava.MethodCall#getMember <em>Member</em>}</li>
 *   <li>{@link org.tetrabox.minijava.xminijavamt.miniJava.MethodCall#getArgs <em>Args</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.xminijavamt.miniJava.MiniJavaPackage#getMethodCall()
 * @model
 * @generated
 */
public interface MethodCall extends Expression {
	/**
	 * Returns the value of the '<em><b>Receiver</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Receiver</em>' containment reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Receiver</em>' containment reference.
	 * @see #setReceiver(Expression)
	 * @see org.tetrabox.minijava.xminijavamt.miniJava.MiniJavaPackage#getMethodCall_Receiver()
	 * @model containment="true"
	 * @generated
	 */
	Expression getReceiver();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.xminijavamt.miniJava.MethodCall#getReceiver <em>Receiver</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Receiver</em>' containment reference.
	 * @see #getReceiver()
	 * @generated
	 */
	void setReceiver(Expression value);

	/**
	 * Returns the value of the '<em><b>Member</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Member</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Member</em>' reference.
	 * @see #setMember(Method)
	 * @see org.tetrabox.minijava.xminijavamt.miniJava.MiniJavaPackage#getMethodCall_Member()
	 * @model
	 * @generated
	 */
	Method getMember();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.xminijavamt.miniJava.MethodCall#getMember <em>Member</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Member</em>' reference.
	 * @see #getMember()
	 * @generated
	 */
	void setMember(Method value);

	/**
	 * Returns the value of the '<em><b>Args</b></em>' containment reference list.
	 * The list contents are of type {@link org.tetrabox.minijava.xminijavamt.miniJava.Expression}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Args</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Args</em>' containment reference list.
	 * @see org.tetrabox.minijava.xminijavamt.miniJava.MiniJavaPackage#getMethodCall_Args()
	 * @model containment="true"
	 * @generated
	 */
	EList<Expression> getArgs();

} // MethodCall
