/**
 */
package org.tetrabox.minijava.xminijava.miniJava;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Type Declaration</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.xminijava.miniJava.TypeDeclaration#getAccessLevel <em>Access Level</em>}</li>
 *   <li>{@link org.tetrabox.minijava.xminijava.miniJava.TypeDeclaration#getImplements <em>Implements</em>}</li>
 *   <li>{@link org.tetrabox.minijava.xminijava.miniJava.TypeDeclaration#getMembers <em>Members</em>}</li>
 * </ul>
 *
 * @see org.tetrabox.minijava.xminijava.miniJava.MiniJavaPackage#getTypeDeclaration()
 * @model
 * @generated
 */
public interface TypeDeclaration extends NamedElement {
	/**
	 * Returns the value of the '<em><b>Access Level</b></em>' attribute.
	 * The literals are from the enumeration {@link org.tetrabox.minijava.xminijava.miniJava.AccessLevel}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Access Level</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Access Level</em>' attribute.
	 * @see org.tetrabox.minijava.xminijava.miniJava.AccessLevel
	 * @see #setAccessLevel(AccessLevel)
	 * @see org.tetrabox.minijava.xminijava.miniJava.MiniJavaPackage#getTypeDeclaration_AccessLevel()
	 * @model
	 * @generated
	 */
	AccessLevel getAccessLevel();

	/**
	 * Sets the value of the '{@link org.tetrabox.minijava.xminijava.miniJava.TypeDeclaration#getAccessLevel <em>Access Level</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Access Level</em>' attribute.
	 * @see org.tetrabox.minijava.xminijava.miniJava.AccessLevel
	 * @see #getAccessLevel()
	 * @generated
	 */
	void setAccessLevel(AccessLevel value);

	/**
	 * Returns the value of the '<em><b>Implements</b></em>' reference list.
	 * The list contents are of type {@link org.tetrabox.minijava.xminijava.miniJava.Interface}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Implements</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Implements</em>' reference list.
	 * @see org.tetrabox.minijava.xminijava.miniJava.MiniJavaPackage#getTypeDeclaration_Implements()
	 * @model
	 * @generated
	 */
	EList<Interface> getImplements();

	/**
	 * Returns the value of the '<em><b>Members</b></em>' containment reference list.
	 * The list contents are of type {@link org.tetrabox.minijava.xminijava.miniJava.Member}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Members</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Members</em>' containment reference list.
	 * @see org.tetrabox.minijava.xminijava.miniJava.MiniJavaPackage#getTypeDeclaration_Members()
	 * @model containment="true"
	 * @generated
	 */
	EList<Member> getMembers();

} // TypeDeclaration
