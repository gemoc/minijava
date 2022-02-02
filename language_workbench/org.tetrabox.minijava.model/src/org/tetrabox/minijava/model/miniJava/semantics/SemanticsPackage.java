/**
 */
package org.tetrabox.minijava.model.miniJava.semantics;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each operation of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see org.tetrabox.minijava.model.miniJava.semantics.SemanticsFactory
 * @model kind="package"
 * @generated
 */
public interface SemanticsPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "semantics";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "http://org.tetrabox.minijava.xminijava/miniJava/semantics";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "semantics";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	SemanticsPackage eINSTANCE = org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl.init();

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ContextImpl <em>Context</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ContextImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getContext()
	 * @generated
	 */
	int CONTEXT = 0;

	/**
	 * The feature id for the '<em><b>Bindings</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT__BINDINGS = 0;

	/**
	 * The feature id for the '<em><b>Parent Context</b></em>' container reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT__PARENT_CONTEXT = 1;

	/**
	 * The feature id for the '<em><b>Child Context</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT__CHILD_CONTEXT = 2;

	/**
	 * The number of structural features of the '<em>Context</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT_FEATURE_COUNT = 3;

	/**
	 * The number of operations of the '<em>Context</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ValueImpl <em>Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getValue()
	 * @generated
	 */
	int VALUE = 1;

	/**
	 * The number of structural features of the '<em>Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VALUE_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VALUE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.IntegerValueImpl <em>Integer Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.IntegerValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getIntegerValue()
	 * @generated
	 */
	int INTEGER_VALUE = 2;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_VALUE__VALUE = VALUE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Integer Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Integer Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.SymbolBindingImpl <em>Symbol Binding</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SymbolBindingImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getSymbolBinding()
	 * @generated
	 */
	int SYMBOL_BINDING = 3;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_BINDING__VALUE = 0;

	/**
	 * The feature id for the '<em><b>Symbol</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_BINDING__SYMBOL = 1;

	/**
	 * The number of structural features of the '<em>Symbol Binding</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_BINDING_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Symbol Binding</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_BINDING_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.FieldBindingImpl <em>Field Binding</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.FieldBindingImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getFieldBinding()
	 * @generated
	 */
	int FIELD_BINDING = 4;

	/**
	 * The feature id for the '<em><b>Field</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_BINDING__FIELD = 0;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_BINDING__VALUE = 1;

	/**
	 * The number of structural features of the '<em>Field Binding</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_BINDING_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Field Binding</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_BINDING_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.StringValueImpl <em>String Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.StringValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getStringValue()
	 * @generated
	 */
	int STRING_VALUE = 5;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_VALUE__VALUE = VALUE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>String Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>String Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.BooleanValueImpl <em>Boolean Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.BooleanValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getBooleanValue()
	 * @generated
	 */
	int BOOLEAN_VALUE = 6;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_VALUE__VALUE = VALUE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Boolean Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Boolean Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.OutputStreamImpl <em>Output Stream</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.OutputStreamImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getOutputStream()
	 * @generated
	 */
	int OUTPUT_STREAM = 7;

	/**
	 * The feature id for the '<em><b>Stream</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTPUT_STREAM__STREAM = 0;

	/**
	 * The number of structural features of the '<em>Output Stream</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTPUT_STREAM_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Output Stream</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTPUT_STREAM_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.StateImpl <em>State</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.StateImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getState()
	 * @generated
	 */
	int STATE = 8;

	/**
	 * The feature id for the '<em><b>Root Frame</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE__ROOT_FRAME = 0;

	/**
	 * The feature id for the '<em><b>Objects Heap</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE__OBJECTS_HEAP = 1;

	/**
	 * The feature id for the '<em><b>Output Stream</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE__OUTPUT_STREAM = 2;

	/**
	 * The feature id for the '<em><b>Arrays Heap</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE__ARRAYS_HEAP = 3;

	/**
	 * The number of structural features of the '<em>State</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE_FEATURE_COUNT = 4;

	/**
	 * The number of operations of the '<em>State</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.FrameImpl <em>Frame</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.FrameImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getFrame()
	 * @generated
	 */
	int FRAME = 9;

	/**
	 * The feature id for the '<em><b>Call</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME__CALL = 0;

	/**
	 * The feature id for the '<em><b>Instance</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME__INSTANCE = 1;

	/**
	 * The feature id for the '<em><b>Child Frame</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME__CHILD_FRAME = 2;

	/**
	 * The feature id for the '<em><b>Parent Frame</b></em>' container reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME__PARENT_FRAME = 3;

	/**
	 * The feature id for the '<em><b>Root Context</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME__ROOT_CONTEXT = 4;

	/**
	 * The feature id for the '<em><b>Return Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME__RETURN_VALUE = 5;

	/**
	 * The number of structural features of the '<em>Frame</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME_FEATURE_COUNT = 6;

	/**
	 * The number of operations of the '<em>Frame</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.NullValueImpl <em>Null Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.NullValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getNullValue()
	 * @generated
	 */
	int NULL_VALUE = 10;

	/**
	 * The number of structural features of the '<em>Null Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Null Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.CallImpl <em>Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.CallImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getCall()
	 * @generated
	 */
	int CALL = 11;

	/**
	 * The number of structural features of the '<em>Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CALL_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CALL_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.NewCallImpl <em>New Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.NewCallImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getNewCall()
	 * @generated
	 */
	int NEW_CALL = 12;

	/**
	 * The feature id for the '<em><b>New</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_CALL__NEW = CALL_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>New Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_CALL_FEATURE_COUNT = CALL_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>New Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_CALL_OPERATION_COUNT = CALL_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.MethodCall2Impl <em>Method Call2</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.MethodCall2Impl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getMethodCall2()
	 * @generated
	 */
	int METHOD_CALL2 = 13;

	/**
	 * The feature id for the '<em><b>Methodcall</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL2__METHODCALL = CALL_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Method Call2</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL2_FEATURE_COUNT = CALL_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Method Call2</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL2_OPERATION_COUNT = CALL_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectInstanceImpl <em>Object Instance</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectInstanceImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getObjectInstance()
	 * @generated
	 */
	int OBJECT_INSTANCE = 14;

	/**
	 * The feature id for the '<em><b>Fieldbindings</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_INSTANCE__FIELDBINDINGS = 0;

	/**
	 * The feature id for the '<em><b>Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_INSTANCE__TYPE = 1;

	/**
	 * The number of structural features of the '<em>Object Instance</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_INSTANCE_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Object Instance</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_INSTANCE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayInstanceImpl <em>Array Instance</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayInstanceImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getArrayInstance()
	 * @generated
	 */
	int ARRAY_INSTANCE = 15;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_INSTANCE__VALUE = 0;

	/**
	 * The feature id for the '<em><b>Size</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_INSTANCE__SIZE = 1;

	/**
	 * The number of structural features of the '<em>Array Instance</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_INSTANCE_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Array Instance</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_INSTANCE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectRefValueImpl <em>Object Ref Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectRefValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getObjectRefValue()
	 * @generated
	 */
	int OBJECT_REF_VALUE = 16;

	/**
	 * The feature id for the '<em><b>Instance</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_REF_VALUE__INSTANCE = VALUE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Object Ref Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_REF_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_REF_VALUE___COPY = VALUE_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_REF_VALUE___CUSTOM_TO_STRING = VALUE_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>Object Ref Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_REF_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayRefValueImpl <em>Array Ref Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayRefValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getArrayRefValue()
	 * @generated
	 */
	int ARRAY_REF_VALUE = 17;

	/**
	 * The feature id for the '<em><b>Instance</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_REF_VALUE__INSTANCE = VALUE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Array Ref Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_REF_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_REF_VALUE___COPY = VALUE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Array Ref Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_REF_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 1;


	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.Context <em>Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Context
	 * @generated
	 */
	EClass getContext();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getBindings <em>Bindings</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Bindings</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Context#getBindings()
	 * @see #getContext()
	 * @generated
	 */
	EReference getContext_Bindings();

	/**
	 * Returns the meta object for the container reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getParentContext <em>Parent Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the container reference '<em>Parent Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Context#getParentContext()
	 * @see #getContext()
	 * @generated
	 */
	EReference getContext_ParentContext();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Context#getChildContext <em>Child Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Child Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Context#getChildContext()
	 * @see #getContext()
	 * @generated
	 */
	EReference getContext_ChildContext();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.Value <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Value
	 * @generated
	 */
	EClass getValue();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.IntegerValue <em>Integer Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Integer Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.IntegerValue
	 * @generated
	 */
	EClass getIntegerValue();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.semantics.IntegerValue#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.IntegerValue#getValue()
	 * @see #getIntegerValue()
	 * @generated
	 */
	EAttribute getIntegerValue_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding <em>Symbol Binding</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Symbol Binding</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding
	 * @generated
	 */
	EClass getSymbolBinding();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding#getValue()
	 * @see #getSymbolBinding()
	 * @generated
	 */
	EReference getSymbolBinding_Value();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding#getSymbol <em>Symbol</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Symbol</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.SymbolBinding#getSymbol()
	 * @see #getSymbolBinding()
	 * @generated
	 */
	EReference getSymbolBinding_Symbol();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding <em>Field Binding</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Field Binding</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.FieldBinding
	 * @generated
	 */
	EClass getFieldBinding();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getField <em>Field</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Field</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getField()
	 * @see #getFieldBinding()
	 * @generated
	 */
	EReference getFieldBinding_Field();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.FieldBinding#getValue()
	 * @see #getFieldBinding()
	 * @generated
	 */
	EReference getFieldBinding_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.StringValue <em>String Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.StringValue
	 * @generated
	 */
	EClass getStringValue();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.semantics.StringValue#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.StringValue#getValue()
	 * @see #getStringValue()
	 * @generated
	 */
	EAttribute getStringValue_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.BooleanValue <em>Boolean Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Boolean Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.BooleanValue
	 * @generated
	 */
	EClass getBooleanValue();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.semantics.BooleanValue#isValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.BooleanValue#isValue()
	 * @see #getBooleanValue()
	 * @generated
	 */
	EAttribute getBooleanValue_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.OutputStream <em>Output Stream</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Output Stream</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.OutputStream
	 * @generated
	 */
	EClass getOutputStream();

	/**
	 * Returns the meta object for the attribute list '{@link org.tetrabox.minijava.model.miniJava.semantics.OutputStream#getStream <em>Stream</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Stream</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.OutputStream#getStream()
	 * @see #getOutputStream()
	 * @generated
	 */
	EAttribute getOutputStream_Stream();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.State <em>State</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>State</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.State
	 * @generated
	 */
	EClass getState();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.State#getRootFrame <em>Root Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Root Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.State#getRootFrame()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_RootFrame();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.semantics.State#getObjectsHeap <em>Objects Heap</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Objects Heap</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.State#getObjectsHeap()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_ObjectsHeap();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.State#getOutputStream <em>Output Stream</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Output Stream</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.State#getOutputStream()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_OutputStream();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.semantics.State#getArraysHeap <em>Arrays Heap</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Arrays Heap</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.State#getArraysHeap()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_ArraysHeap();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame <em>Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame
	 * @generated
	 */
	EClass getFrame();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame#getCall <em>Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame#getCall()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_Call();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame#getInstance <em>Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame#getInstance()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_Instance();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame#getChildFrame <em>Child Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Child Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame#getChildFrame()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_ChildFrame();

	/**
	 * Returns the meta object for the container reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame#getParentFrame <em>Parent Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the container reference '<em>Parent Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame#getParentFrame()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_ParentFrame();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame#getRootContext <em>Root Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Root Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame#getRootContext()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_RootContext();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.semantics.Frame#getReturnValue <em>Return Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Return Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Frame#getReturnValue()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_ReturnValue();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.NullValue <em>Null Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Null Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.NullValue
	 * @generated
	 */
	EClass getNullValue();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.Call <em>Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.Call
	 * @generated
	 */
	EClass getCall();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.NewCall <em>New Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>New Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.NewCall
	 * @generated
	 */
	EClass getNewCall();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.NewCall#getNew <em>New</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>New</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.NewCall#getNew()
	 * @see #getNewCall()
	 * @generated
	 */
	EReference getNewCall_New();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.MethodCall2 <em>Method Call2</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Method Call2</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.MethodCall2
	 * @generated
	 */
	EClass getMethodCall2();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.MethodCall2#getMethodcall <em>Methodcall</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Methodcall</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.MethodCall2#getMethodcall()
	 * @see #getMethodCall2()
	 * @generated
	 */
	EReference getMethodCall2_Methodcall();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance <em>Object Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Object Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance
	 * @generated
	 */
	EClass getObjectInstance();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance#getFieldbindings <em>Fieldbindings</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Fieldbindings</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance#getFieldbindings()
	 * @see #getObjectInstance()
	 * @generated
	 */
	EReference getObjectInstance_Fieldbindings();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Type</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectInstance#getType()
	 * @see #getObjectInstance()
	 * @generated
	 */
	EReference getObjectInstance_Type();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance <em>Array Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance
	 * @generated
	 */
	EClass getArrayInstance();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance#getValue()
	 * @see #getArrayInstance()
	 * @generated
	 */
	EReference getArrayInstance_Value();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance#getSize <em>Size</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Size</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ArrayInstance#getSize()
	 * @see #getArrayInstance()
	 * @generated
	 */
	EAttribute getArrayInstance_Size();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue <em>Object Ref Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Object Ref Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue
	 * @generated
	 */
	EClass getObjectRefValue();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue#getInstance <em>Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue#getInstance()
	 * @see #getObjectRefValue()
	 * @generated
	 */
	EReference getObjectRefValue_Instance();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue#copy()
	 * @generated
	 */
	EOperation getObjectRefValue__Copy();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue#customToString() <em>Custom To String</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Custom To String</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ObjectRefValue#customToString()
	 * @generated
	 */
	EOperation getObjectRefValue__CustomToString();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue <em>Array Ref Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Ref Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue
	 * @generated
	 */
	EClass getArrayRefValue();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue#getInstance <em>Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue#getInstance()
	 * @see #getArrayRefValue()
	 * @generated
	 */
	EReference getArrayRefValue_Instance();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.semantics.ArrayRefValue#copy()
	 * @generated
	 */
	EOperation getArrayRefValue__Copy();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	SemanticsFactory getSemanticsFactory();

	/**
	 * <!-- begin-user-doc -->
	 * Defines literals for the meta objects that represent
	 * <ul>
	 *   <li>each class,</li>
	 *   <li>each feature of each class,</li>
	 *   <li>each operation of each class,</li>
	 *   <li>each enum,</li>
	 *   <li>and each data type</li>
	 * </ul>
	 * <!-- end-user-doc -->
	 * @generated
	 */
	interface Literals {
		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ContextImpl <em>Context</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ContextImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getContext()
		 * @generated
		 */
		EClass CONTEXT = eINSTANCE.getContext();

		/**
		 * The meta object literal for the '<em><b>Bindings</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CONTEXT__BINDINGS = eINSTANCE.getContext_Bindings();

		/**
		 * The meta object literal for the '<em><b>Parent Context</b></em>' container reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CONTEXT__PARENT_CONTEXT = eINSTANCE.getContext_ParentContext();

		/**
		 * The meta object literal for the '<em><b>Child Context</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CONTEXT__CHILD_CONTEXT = eINSTANCE.getContext_ChildContext();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ValueImpl <em>Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getValue()
		 * @generated
		 */
		EClass VALUE = eINSTANCE.getValue();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.IntegerValueImpl <em>Integer Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.IntegerValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getIntegerValue()
		 * @generated
		 */
		EClass INTEGER_VALUE = eINSTANCE.getIntegerValue();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INTEGER_VALUE__VALUE = eINSTANCE.getIntegerValue_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.SymbolBindingImpl <em>Symbol Binding</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SymbolBindingImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getSymbolBinding()
		 * @generated
		 */
		EClass SYMBOL_BINDING = eINSTANCE.getSymbolBinding();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SYMBOL_BINDING__VALUE = eINSTANCE.getSymbolBinding_Value();

		/**
		 * The meta object literal for the '<em><b>Symbol</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SYMBOL_BINDING__SYMBOL = eINSTANCE.getSymbolBinding_Symbol();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.FieldBindingImpl <em>Field Binding</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.FieldBindingImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getFieldBinding()
		 * @generated
		 */
		EClass FIELD_BINDING = eINSTANCE.getFieldBinding();

		/**
		 * The meta object literal for the '<em><b>Field</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD_BINDING__FIELD = eINSTANCE.getFieldBinding_Field();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD_BINDING__VALUE = eINSTANCE.getFieldBinding_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.StringValueImpl <em>String Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.StringValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getStringValue()
		 * @generated
		 */
		EClass STRING_VALUE = eINSTANCE.getStringValue();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STRING_VALUE__VALUE = eINSTANCE.getStringValue_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.BooleanValueImpl <em>Boolean Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.BooleanValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getBooleanValue()
		 * @generated
		 */
		EClass BOOLEAN_VALUE = eINSTANCE.getBooleanValue();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BOOLEAN_VALUE__VALUE = eINSTANCE.getBooleanValue_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.OutputStreamImpl <em>Output Stream</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.OutputStreamImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getOutputStream()
		 * @generated
		 */
		EClass OUTPUT_STREAM = eINSTANCE.getOutputStream();

		/**
		 * The meta object literal for the '<em><b>Stream</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute OUTPUT_STREAM__STREAM = eINSTANCE.getOutputStream_Stream();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.StateImpl <em>State</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.StateImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getState()
		 * @generated
		 */
		EClass STATE = eINSTANCE.getState();

		/**
		 * The meta object literal for the '<em><b>Root Frame</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference STATE__ROOT_FRAME = eINSTANCE.getState_RootFrame();

		/**
		 * The meta object literal for the '<em><b>Objects Heap</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference STATE__OBJECTS_HEAP = eINSTANCE.getState_ObjectsHeap();

		/**
		 * The meta object literal for the '<em><b>Output Stream</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference STATE__OUTPUT_STREAM = eINSTANCE.getState_OutputStream();

		/**
		 * The meta object literal for the '<em><b>Arrays Heap</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference STATE__ARRAYS_HEAP = eINSTANCE.getState_ArraysHeap();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.FrameImpl <em>Frame</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.FrameImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getFrame()
		 * @generated
		 */
		EClass FRAME = eINSTANCE.getFrame();

		/**
		 * The meta object literal for the '<em><b>Call</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FRAME__CALL = eINSTANCE.getFrame_Call();

		/**
		 * The meta object literal for the '<em><b>Instance</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FRAME__INSTANCE = eINSTANCE.getFrame_Instance();

		/**
		 * The meta object literal for the '<em><b>Child Frame</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FRAME__CHILD_FRAME = eINSTANCE.getFrame_ChildFrame();

		/**
		 * The meta object literal for the '<em><b>Parent Frame</b></em>' container reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FRAME__PARENT_FRAME = eINSTANCE.getFrame_ParentFrame();

		/**
		 * The meta object literal for the '<em><b>Root Context</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FRAME__ROOT_CONTEXT = eINSTANCE.getFrame_RootContext();

		/**
		 * The meta object literal for the '<em><b>Return Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FRAME__RETURN_VALUE = eINSTANCE.getFrame_ReturnValue();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.NullValueImpl <em>Null Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.NullValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getNullValue()
		 * @generated
		 */
		EClass NULL_VALUE = eINSTANCE.getNullValue();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.CallImpl <em>Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.CallImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getCall()
		 * @generated
		 */
		EClass CALL = eINSTANCE.getCall();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.NewCallImpl <em>New Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.NewCallImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getNewCall()
		 * @generated
		 */
		EClass NEW_CALL = eINSTANCE.getNewCall();

		/**
		 * The meta object literal for the '<em><b>New</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_CALL__NEW = eINSTANCE.getNewCall_New();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.MethodCall2Impl <em>Method Call2</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.MethodCall2Impl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getMethodCall2()
		 * @generated
		 */
		EClass METHOD_CALL2 = eINSTANCE.getMethodCall2();

		/**
		 * The meta object literal for the '<em><b>Methodcall</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL2__METHODCALL = eINSTANCE.getMethodCall2_Methodcall();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectInstanceImpl <em>Object Instance</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectInstanceImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getObjectInstance()
		 * @generated
		 */
		EClass OBJECT_INSTANCE = eINSTANCE.getObjectInstance();

		/**
		 * The meta object literal for the '<em><b>Fieldbindings</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OBJECT_INSTANCE__FIELDBINDINGS = eINSTANCE.getObjectInstance_Fieldbindings();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OBJECT_INSTANCE__TYPE = eINSTANCE.getObjectInstance_Type();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayInstanceImpl <em>Array Instance</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayInstanceImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getArrayInstance()
		 * @generated
		 */
		EClass ARRAY_INSTANCE = eINSTANCE.getArrayInstance();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_INSTANCE__VALUE = eINSTANCE.getArrayInstance_Value();

		/**
		 * The meta object literal for the '<em><b>Size</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute ARRAY_INSTANCE__SIZE = eINSTANCE.getArrayInstance_Size();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectRefValueImpl <em>Object Ref Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ObjectRefValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getObjectRefValue()
		 * @generated
		 */
		EClass OBJECT_REF_VALUE = eINSTANCE.getObjectRefValue();

		/**
		 * The meta object literal for the '<em><b>Instance</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OBJECT_REF_VALUE__INSTANCE = eINSTANCE.getObjectRefValue_Instance();

		/**
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation OBJECT_REF_VALUE___COPY = eINSTANCE.getObjectRefValue__Copy();

		/**
		 * The meta object literal for the '<em><b>Custom To String</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation OBJECT_REF_VALUE___CUSTOM_TO_STRING = eINSTANCE.getObjectRefValue__CustomToString();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayRefValueImpl <em>Array Ref Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.ArrayRefValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.semantics.impl.SemanticsPackageImpl#getArrayRefValue()
		 * @generated
		 */
		EClass ARRAY_REF_VALUE = eINSTANCE.getArrayRefValue();

		/**
		 * The meta object literal for the '<em><b>Instance</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_REF_VALUE__INSTANCE = eINSTANCE.getArrayRefValue_Instance();

		/**
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation ARRAY_REF_VALUE___COPY = eINSTANCE.getArrayRefValue__Copy();

	}

} //SemanticsPackage
