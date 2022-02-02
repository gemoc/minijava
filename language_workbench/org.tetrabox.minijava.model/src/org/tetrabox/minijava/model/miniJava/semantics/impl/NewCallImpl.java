/**
 */
package org.tetrabox.minijava.model.miniJava.semantics.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.tetrabox.minijava.model.miniJava.NewObject;

import org.tetrabox.minijava.model.miniJava.semantics.NewCall;
import org.tetrabox.minijava.model.miniJava.semantics.SemanticsPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>New Call</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link org.tetrabox.minijava.model.miniJava.semantics.impl.NewCallImpl#getNew <em>New</em>}</li>
 * </ul>
 *
 * @generated
 */
public class NewCallImpl extends CallImpl implements NewCall {
	/**
	 * The cached value of the '{@link #getNew() <em>New</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getNew()
	 * @generated
	 * @ordered
	 */
	protected NewObject new_;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected NewCallImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return SemanticsPackage.Literals.NEW_CALL;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NewObject getNew() {
		if (new_ != null && new_.eIsProxy()) {
			InternalEObject oldNew = (InternalEObject)new_;
			new_ = (NewObject)eResolveProxy(oldNew);
			if (new_ != oldNew) {
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, SemanticsPackage.NEW_CALL__NEW, oldNew, new_));
			}
		}
		return new_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NewObject basicGetNew() {
		return new_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setNew(NewObject newNew) {
		NewObject oldNew = new_;
		new_ = newNew;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, SemanticsPackage.NEW_CALL__NEW, oldNew, new_));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case SemanticsPackage.NEW_CALL__NEW:
				if (resolve) return getNew();
				return basicGetNew();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eSet(int featureID, Object newValue) {
		switch (featureID) {
			case SemanticsPackage.NEW_CALL__NEW:
				setNew((NewObject)newValue);
				return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eUnset(int featureID) {
		switch (featureID) {
			case SemanticsPackage.NEW_CALL__NEW:
				setNew((NewObject)null);
				return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID) {
		switch (featureID) {
			case SemanticsPackage.NEW_CALL__NEW:
				return new_ != null;
		}
		return super.eIsSet(featureID);
	}

} //NewCallImpl
