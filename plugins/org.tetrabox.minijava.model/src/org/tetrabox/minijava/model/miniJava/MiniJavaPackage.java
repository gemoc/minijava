/**
 */
package org.tetrabox.minijava.model.miniJava;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
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
 * @see org.tetrabox.minijava.model.miniJava.MiniJavaFactory
 * @model kind="package"
 * @generated
 */
public interface MiniJavaPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "miniJava";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "http://org.tetrabox.minijava.xminijava/miniJava/";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "miniJava";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	MiniJavaPackage eINSTANCE = org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl.init();

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ProgramImpl <em>Program</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ProgramImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getProgram()
	 * @generated
	 */
	int PROGRAM = 0;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__NAME = 0;

	/**
	 * The feature id for the '<em><b>Imports</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__IMPORTS = 1;

	/**
	 * The feature id for the '<em><b>Classes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__CLASSES = 2;

	/**
	 * The feature id for the '<em><b>State</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__STATE = 3;

	/**
	 * The number of structural features of the '<em>Program</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM_FEATURE_COUNT = 4;

	/**
	 * The operation id for the '<em>Main</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM___MAIN = 0;

	/**
	 * The operation id for the '<em>Initialize</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM___INITIALIZE__ELIST = 1;

	/**
	 * The operation id for the '<em>Execute</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM___EXECUTE = 2;

	/**
	 * The number of operations of the '<em>Program</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM_OPERATION_COUNT = 3;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ImportImpl <em>Import</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ImportImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getImport()
	 * @generated
	 */
	int IMPORT = 1;

	/**
	 * The feature id for the '<em><b>Imported Namespace</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT__IMPORTED_NAMESPACE = 0;

	/**
	 * The number of structural features of the '<em>Import</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Import</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl <em>Named Element</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNamedElement()
	 * @generated
	 */
	int NAMED_ELEMENT = 19;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT__NAME = 0;

	/**
	 * The number of structural features of the '<em>Named Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Named Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl <em>Type Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeDeclaration()
	 * @generated
	 */
	int TYPE_DECLARATION = 2;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The feature id for the '<em><b>Access Level</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__ACCESS_LEVEL = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Implements</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__IMPLEMENTS = NAMED_ELEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Members</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__MEMBERS = NAMED_ELEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Type Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Type Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassImpl <em>Class</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ClassImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClass_()
	 * @generated
	 */
	int CLASS = 3;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__NAME = TYPE_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Access Level</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__ACCESS_LEVEL = TYPE_DECLARATION__ACCESS_LEVEL;

	/**
	 * The feature id for the '<em><b>Implements</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IMPLEMENTS = TYPE_DECLARATION__IMPLEMENTS;

	/**
	 * The feature id for the '<em><b>Members</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__MEMBERS = TYPE_DECLARATION__MEMBERS;

	/**
	 * The feature id for the '<em><b>Abstract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__ABSTRACT = TYPE_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Super Class</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__SUPER_CLASS = TYPE_DECLARATION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_FEATURE_COUNT = TYPE_DECLARATION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_OPERATION_COUNT = TYPE_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl <em>Interface</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInterface()
	 * @generated
	 */
	int INTERFACE = 4;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__NAME = TYPE_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Access Level</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__ACCESS_LEVEL = TYPE_DECLARATION__ACCESS_LEVEL;

	/**
	 * The feature id for the '<em><b>Implements</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__IMPLEMENTS = TYPE_DECLARATION__IMPLEMENTS;

	/**
	 * The feature id for the '<em><b>Members</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__MEMBERS = TYPE_DECLARATION__MEMBERS;

	/**
	 * The number of structural features of the '<em>Interface</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE_FEATURE_COUNT = TYPE_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Interface</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE_OPERATION_COUNT = TYPE_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl <em>Typed Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypedDeclaration()
	 * @generated
	 */
	int TYPED_DECLARATION = 20;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION__TYPE_REF = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Typed Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Typed Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MemberImpl <em>Member</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MemberImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMember()
	 * @generated
	 */
	int MEMBER = 5;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER__NAME = TYPED_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER__TYPE_REF = TYPED_DECLARATION__TYPE_REF;

	/**
	 * The feature id for the '<em><b>Access</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER__ACCESS = TYPED_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Member</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Member</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER_OPERATION_COUNT = TYPED_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodImpl <em>Method</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MethodImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethod()
	 * @generated
	 */
	int METHOD = 6;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__NAME = MEMBER__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__TYPE_REF = MEMBER__TYPE_REF;

	/**
	 * The feature id for the '<em><b>Access</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__ACCESS = MEMBER__ACCESS;

	/**
	 * The feature id for the '<em><b>Abstract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__ABSTRACT = MEMBER_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Static</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__STATIC = MEMBER_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Params</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__PARAMS = MEMBER_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__BODY = MEMBER_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Method</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_FEATURE_COUNT = MEMBER_FEATURE_COUNT + 4;

	/**
	 * The operation id for the '<em>Call</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD___CALL__STATE = MEMBER_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Find Override</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD___FIND_OVERRIDE__CLASS = MEMBER_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>Method</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_OPERATION_COUNT = MEMBER_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolImpl <em>Symbol</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbol()
	 * @generated
	 */
	int SYMBOL = 21;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL__NAME = TYPED_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL__TYPE_REF = TYPED_DECLARATION__TYPE_REF;

	/**
	 * The number of structural features of the '<em>Symbol</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Symbol</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_OPERATION_COUNT = TYPED_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ParameterImpl <em>Parameter</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ParameterImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getParameter()
	 * @generated
	 */
	int PARAMETER = 7;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__NAME = SYMBOL__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__TYPE_REF = SYMBOL__TYPE_REF;

	/**
	 * The number of structural features of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_FEATURE_COUNT = SYMBOL_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER___COMPARE__PARAMETER = SYMBOL_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_OPERATION_COUNT = SYMBOL_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldImpl <em>Field</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.FieldImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getField()
	 * @generated
	 */
	int FIELD = 8;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__NAME = MEMBER__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__TYPE_REF = MEMBER__TYPE_REF;

	/**
	 * The feature id for the '<em><b>Access</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__ACCESS = MEMBER__ACCESS;

	/**
	 * The feature id for the '<em><b>Default Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__DEFAULT_VALUE = MEMBER_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Field</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_FEATURE_COUNT = MEMBER_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Field</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_OPERATION_COUNT = MEMBER_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StatementImpl <em>Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStatement()
	 * @generated
	 */
	int STATEMENT = 10;

	/**
	 * The number of structural features of the '<em>Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT_FEATURE_COUNT = 0;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT___EVALUATE_STATEMENT__STATE = 0;

	/**
	 * The number of operations of the '<em>Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT_OPERATION_COUNT = 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BlockImpl <em>Block</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BlockImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBlock()
	 * @generated
	 */
	int BLOCK = 9;

	/**
	 * The feature id for the '<em><b>Statements</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK__STATEMENTS = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Block</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement Keep Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK___EVALUATE_STATEMENT_KEEP_CONTEXT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>Block</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl <em>Print Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPrintStatement()
	 * @generated
	 */
	int PRINT_STATEMENT = 11;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Print Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Print Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ReturnImpl <em>Return</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ReturnImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getReturn()
	 * @generated
	 */
	int RETURN = 12;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Return</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Return</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl <em>If Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIfStatement()
	 * @generated
	 */
	int IF_STATEMENT = 13;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Then Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT__THEN_BLOCK = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Else Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT__ELSE_BLOCK = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>If Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>If Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl <em>While Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getWhileStatement()
	 * @generated
	 */
	int WHILE_STATEMENT = 14;

	/**
	 * The feature id for the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT__CONDITION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT__BLOCK = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>While Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>While Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl <em>For Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getForStatement()
	 * @generated
	 */
	int FOR_STATEMENT = 15;

	/**
	 * The feature id for the '<em><b>Declaration</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__DECLARATION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__CONDITION = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Progression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__PROGRESSION = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__BLOCK = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>For Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 4;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>For Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl <em>Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeRef()
	 * @generated
	 */
	int TYPE_REF = 16;

	/**
	 * The number of structural features of the '<em>Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_REF_FEATURE_COUNT = 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_REF___COMPARE__TYPEREF = 0;

	/**
	 * The number of operations of the '<em>Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_REF_OPERATION_COUNT = 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl <em>Single Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSingleTypeRef()
	 * @generated
	 */
	int SINGLE_TYPE_REF = 17;

	/**
	 * The number of structural features of the '<em>Single Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_TYPE_REF_FEATURE_COUNT = TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_TYPE_REF___COMPARE__TYPEREF = TYPE_REF___COMPARE__TYPEREF;

	/**
	 * The number of operations of the '<em>Single Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_TYPE_REF_OPERATION_COUNT = TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl <em>Class Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClassRef()
	 * @generated
	 */
	int CLASS_REF = 18;

	/**
	 * The feature id for the '<em><b>Referenced Class</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF__REFERENCED_CLASS = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Class Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF___COMPARE__TYPEREF = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Class Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl <em>Variable Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVariableDeclaration()
	 * @generated
	 */
	int VARIABLE_DECLARATION = 22;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION__NAME = SYMBOL__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION__TYPE_REF = SYMBOL__TYPE_REF;

	/**
	 * The number of structural features of the '<em>Variable Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION_FEATURE_COUNT = SYMBOL_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Variable Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION_OPERATION_COUNT = SYMBOL_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl <em>Assignment</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignment()
	 * @generated
	 */
	int ASSIGNMENT = 23;

	/**
	 * The feature id for the '<em><b>Assignee</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT__ASSIGNEE = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT__VALUE = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Assignment</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Assignment</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl <em>Assignee</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignee()
	 * @generated
	 */
	int ASSIGNEE = 24;

	/**
	 * The number of structural features of the '<em>Assignee</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNEE_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Assignee</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNEE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl <em>Expression</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getExpression()
	 * @generated
	 */
	int EXPRESSION = 25;

	/**
	 * The number of structural features of the '<em>Expression</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION___EVALUATE_STATEMENT__STATE = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION___EVALUATE_EXPRESSION__STATE = STATEMENT_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>Expression</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl <em>Array Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayTypeRef()
	 * @generated
	 */
	int ARRAY_TYPE_REF = 26;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF__TYPE_REF = TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Array Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF_FEATURE_COUNT = TYPE_REF_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF___COMPARE__TYPEREF = TYPE_REF___COMPARE__TYPEREF;

	/**
	 * The number of operations of the '<em>Array Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF_OPERATION_COUNT = TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl <em>Integer Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntegerTypeRef()
	 * @generated
	 */
	int INTEGER_TYPE_REF = 27;

	/**
	 * The number of structural features of the '<em>Integer Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_TYPE_REF___COMPARE__TYPEREF = SINGLE_TYPE_REF___COMPARE__TYPEREF;

	/**
	 * The number of operations of the '<em>Integer Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl <em>Boolean Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBooleanTypeRef()
	 * @generated
	 */
	int BOOLEAN_TYPE_REF = 28;

	/**
	 * The number of structural features of the '<em>Boolean Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_TYPE_REF___COMPARE__TYPEREF = SINGLE_TYPE_REF___COMPARE__TYPEREF;

	/**
	 * The number of operations of the '<em>Boolean Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl <em>String Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringTypeRef()
	 * @generated
	 */
	int STRING_TYPE_REF = 29;

	/**
	 * The number of structural features of the '<em>String Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_TYPE_REF___COMPARE__TYPEREF = SINGLE_TYPE_REF___COMPARE__TYPEREF;

	/**
	 * The number of operations of the '<em>String Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl <em>Void Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVoidTypeRef()
	 * @generated
	 */
	int VOID_TYPE_REF = 30;

	/**
	 * The number of structural features of the '<em>Void Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VOID_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Compare</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VOID_TYPE_REF___COMPARE__TYPEREF = SINGLE_TYPE_REF___COMPARE__TYPEREF;

	/**
	 * The number of operations of the '<em>Void Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VOID_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.OrImpl <em>Or</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.OrImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getOr()
	 * @generated
	 */
	int OR = 31;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Or</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Or</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.AndImpl <em>And</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.AndImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAnd()
	 * @generated
	 */
	int AND = 32;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>And</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>And</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.EqualityImpl <em>Equality</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.EqualityImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getEquality()
	 * @generated
	 */
	int EQUALITY = 33;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Equality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Equality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InequalityImpl <em>Inequality</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InequalityImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInequality()
	 * @generated
	 */
	int INEQUALITY = 34;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inequality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Inequality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl <em>Superior Or Equal</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperiorOrEqual()
	 * @generated
	 */
	int SUPERIOR_OR_EQUAL = 35;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Superior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Superior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl <em>Inferior Or Equal</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferiorOrEqual()
	 * @generated
	 */
	int INFERIOR_OR_EQUAL = 36;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inferior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Inferior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl <em>Superior</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperior()
	 * @generated
	 */
	int SUPERIOR = 37;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Superior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Superior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorImpl <em>Inferior</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferior()
	 * @generated
	 */
	int INFERIOR = 38;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inferior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Inferior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.PlusImpl <em>Plus</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.PlusImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPlus()
	 * @generated
	 */
	int PLUS = 39;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Plus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Plus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MinusImpl <em>Minus</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MinusImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMinus()
	 * @generated
	 */
	int MINUS = 40;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Minus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Minus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl <em>Multiplication</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMultiplication()
	 * @generated
	 */
	int MULTIPLICATION = 41;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Multiplication</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Multiplication</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.DivisionImpl <em>Division</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.DivisionImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getDivision()
	 * @generated
	 */
	int DIVISION = 42;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Division</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Division</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl <em>Array Access</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayAccess()
	 * @generated
	 */
	int ARRAY_ACCESS = 43;

	/**
	 * The feature id for the '<em><b>Object</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS__OBJECT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Index</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS__INDEX = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Array Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Array Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl <em>Array Length</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayLength()
	 * @generated
	 */
	int ARRAY_LENGTH = 44;

	/**
	 * The feature id for the '<em><b>Array</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH__ARRAY = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Array Length</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Array Length</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NotImpl <em>Not</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NotImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNot()
	 * @generated
	 */
	int NOT = 45;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Not</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Not</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NegImpl <em>Neg</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NegImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNeg()
	 * @generated
	 */
	int NEG = 46;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Neg</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Neg</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl <em>Field Access</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFieldAccess()
	 * @generated
	 */
	int FIELD_ACCESS = 47;

	/**
	 * The feature id for the '<em><b>Receiver</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS__RECEIVER = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Field</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS__FIELD = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Field Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Field Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl <em>Method Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethodCall()
	 * @generated
	 */
	int METHOD_CALL = 48;

	/**
	 * The feature id for the '<em><b>Receiver</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL__RECEIVER = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Method</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL__METHOD = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Args</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL__ARGS = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Method Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 3;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Method Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl <em>String Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringConstant()
	 * @generated
	 */
	int STRING_CONSTANT = 49;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT__VALUE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>String Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>String Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl <em>Int Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntConstant()
	 * @generated
	 */
	int INT_CONSTANT = 50;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT__VALUE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Int Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Int Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl <em>Bool Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBoolConstant()
	 * @generated
	 */
	int BOOL_CONSTANT = 51;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT__VALUE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Bool Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Bool Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ThisImpl <em>This</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ThisImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getThis()
	 * @generated
	 */
	int THIS = 52;

	/**
	 * The number of structural features of the '<em>This</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THIS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THIS___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THIS___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>This</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THIS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperImpl <em>Super</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SuperImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuper()
	 * @generated
	 */
	int SUPER = 53;

	/**
	 * The number of structural features of the '<em>Super</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPER_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPER___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPER___EVALUATE_EXPRESSION__STATE = EXPRESSION___EVALUATE_EXPRESSION__STATE;

	/**
	 * The number of operations of the '<em>Super</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPER_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NullImpl <em>Null</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NullImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNull()
	 * @generated
	 */
	int NULL = 54;

	/**
	 * The number of structural features of the '<em>Null</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Null</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl <em>New Object</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewObject()
	 * @generated
	 */
	int NEW_OBJECT = 55;

	/**
	 * The feature id for the '<em><b>Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT__TYPE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Args</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT__ARGS = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>New Object</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>New Object</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl <em>New Array</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewArray()
	 * @generated
	 */
	int NEW_ARRAY = 56;

	/**
	 * The feature id for the '<em><b>Type</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY__TYPE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Size</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY__SIZE = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>New Array</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>New Array</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl <em>Symbol Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbolRef()
	 * @generated
	 */
	int SYMBOL_REF = 57;

	/**
	 * The feature id for the '<em><b>Symbol</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF__SYMBOL = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Symbol Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Evaluate Statement</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF___EVALUATE_STATEMENT__STATE = EXPRESSION___EVALUATE_STATEMENT__STATE;

	/**
	 * The operation id for the '<em>Evaluate Expression</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF___EVALUATE_EXPRESSION__STATE = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Symbol Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ContextImpl <em>Context</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ContextImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getContext()
	 * @generated
	 */
	int CONTEXT = 58;

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
	 * The operation id for the '<em>Create Child Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT___CREATE_CHILD_CONTEXT = 0;

	/**
	 * The operation id for the '<em>Find Binding</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT___FIND_BINDING__SYMBOL = 1;

	/**
	 * The operation id for the '<em>Find Current Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT___FIND_CURRENT_CONTEXT = 2;

	/**
	 * The number of operations of the '<em>Context</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONTEXT_OPERATION_COUNT = 3;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ValueImpl <em>Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getValue()
	 * @generated
	 */
	int VALUE = 59;

	/**
	 * The number of structural features of the '<em>Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VALUE_FEATURE_COUNT = 0;

	/**
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VALUE___CUSTOM_TO_STRING = 0;

	/**
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VALUE___COPY = 1;

	/**
	 * The number of operations of the '<em>Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VALUE_OPERATION_COUNT = 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntegerValueImpl <em>Integer Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IntegerValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntegerValue()
	 * @generated
	 */
	int INTEGER_VALUE = 60;

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
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_VALUE___COPY = VALUE_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_VALUE___CUSTOM_TO_STRING = VALUE_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>Integer Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolBindingImpl <em>Symbol Binding</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolBindingImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbolBinding()
	 * @generated
	 */
	int SYMBOL_BINDING = 61;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldBindingImpl <em>Field Binding</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.FieldBindingImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFieldBinding()
	 * @generated
	 */
	int FIELD_BINDING = 62;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringValueImpl <em>String Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StringValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringValue()
	 * @generated
	 */
	int STRING_VALUE = 63;

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
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_VALUE___COPY = VALUE_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_VALUE___CUSTOM_TO_STRING = VALUE_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>String Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BooleanValueImpl <em>Boolean Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BooleanValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBooleanValue()
	 * @generated
	 */
	int BOOLEAN_VALUE = 64;

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
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_VALUE___CUSTOM_TO_STRING = VALUE_OPERATION_COUNT + 0;

	/**
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_VALUE___COPY = VALUE_OPERATION_COUNT + 1;

	/**
	 * The number of operations of the '<em>Boolean Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.OutputStreamImpl <em>Output Stream</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.OutputStreamImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getOutputStream()
	 * @generated
	 */
	int OUTPUT_STREAM = 65;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StateImpl <em>State</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StateImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getState()
	 * @generated
	 */
	int STATE = 66;

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
	 * The operation id for the '<em>Find Current Frame</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___FIND_CURRENT_FRAME = 0;

	/**
	 * The operation id for the '<em>Find Current Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___FIND_CURRENT_CONTEXT = 1;

	/**
	 * The operation id for the '<em>Println</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___PRINTLN__STRING = 2;

	/**
	 * The operation id for the '<em>Push New Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___PUSH_NEW_CONTEXT = 3;

	/**
	 * The operation id for the '<em>Pop Current Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___POP_CURRENT_CONTEXT = 4;

	/**
	 * The operation id for the '<em>Push New Frame</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___PUSH_NEW_FRAME__OBJECTINSTANCE_CALL_CONTEXT = 5;

	/**
	 * The operation id for the '<em>Pop Current Frame</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE___POP_CURRENT_FRAME = 6;

	/**
	 * The number of operations of the '<em>State</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATE_OPERATION_COUNT = 7;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.FrameImpl <em>Frame</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.FrameImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFrame()
	 * @generated
	 */
	int FRAME = 67;

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
	 * The operation id for the '<em>Find Current Frame</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME___FIND_CURRENT_FRAME = 0;

	/**
	 * The operation id for the '<em>Find Current Context</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME___FIND_CURRENT_CONTEXT = 1;

	/**
	 * The number of operations of the '<em>Frame</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FRAME_OPERATION_COUNT = 2;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NullValueImpl <em>Null Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NullValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNullValue()
	 * @generated
	 */
	int NULL_VALUE = 68;

	/**
	 * The number of structural features of the '<em>Null Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_VALUE_FEATURE_COUNT = VALUE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_VALUE___CUSTOM_TO_STRING = VALUE___CUSTOM_TO_STRING;

	/**
	 * The operation id for the '<em>Copy</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_VALUE___COPY = VALUE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Null Value</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_VALUE_OPERATION_COUNT = VALUE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.CallImpl <em>Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.CallImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getCall()
	 * @generated
	 */
	int CALL = 69;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewCallImpl <em>New Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NewCallImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewCall()
	 * @generated
	 */
	int NEW_CALL = 70;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodCall2Impl <em>Method Call2</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MethodCall2Impl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethodCall2()
	 * @generated
	 */
	int METHOD_CALL2 = 71;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ObjectInstanceImpl <em>Object Instance</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ObjectInstanceImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getObjectInstance()
	 * @generated
	 */
	int OBJECT_INSTANCE = 72;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayInstanceImpl <em>Array Instance</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayInstanceImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayInstance()
	 * @generated
	 */
	int ARRAY_INSTANCE = 73;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ObjectRefValueImpl <em>Object Ref Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ObjectRefValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getObjectRefValue()
	 * @generated
	 */
	int OBJECT_REF_VALUE = 74;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayRefValueImpl <em>Array Ref Value</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayRefValueImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayRefValue()
	 * @generated
	 */
	int ARRAY_REF_VALUE = 75;

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
	 * The operation id for the '<em>Custom To String</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_REF_VALUE___CUSTOM_TO_STRING = VALUE___CUSTOM_TO_STRING;

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
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.AccessLevel <em>Access Level</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.AccessLevel
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAccessLevel()
	 * @generated
	 */
	int ACCESS_LEVEL = 76;


	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Program <em>Program</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Program</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program
	 * @generated
	 */
	EClass getProgram();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Program#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getName()
	 * @see #getProgram()
	 * @generated
	 */
	EAttribute getProgram_Name();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Program#getImports <em>Imports</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Imports</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getImports()
	 * @see #getProgram()
	 * @generated
	 */
	EReference getProgram_Imports();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Program#getClasses <em>Classes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Classes</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getClasses()
	 * @see #getProgram()
	 * @generated
	 */
	EReference getProgram_Classes();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Program#getState <em>State</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>State</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getState()
	 * @see #getProgram()
	 * @generated
	 */
	EReference getProgram_State();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Program#main() <em>Main</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Main</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Program#main()
	 * @generated
	 */
	EOperation getProgram__Main();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Program#initialize(org.eclipse.emf.common.util.EList) <em>Initialize</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Initialize</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Program#initialize(org.eclipse.emf.common.util.EList)
	 * @generated
	 */
	EOperation getProgram__Initialize__EList();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Program#execute() <em>Execute</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Execute</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Program#execute()
	 * @generated
	 */
	EOperation getProgram__Execute();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Import <em>Import</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Import</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Import
	 * @generated
	 */
	EClass getImport();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Import#getImportedNamespace <em>Imported Namespace</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Imported Namespace</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Import#getImportedNamespace()
	 * @see #getImport()
	 * @generated
	 */
	EAttribute getImport_ImportedNamespace();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration <em>Type Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Type Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration
	 * @generated
	 */
	EClass getTypeDeclaration();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration#getAccessLevel <em>Access Level</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Access Level</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration#getAccessLevel()
	 * @see #getTypeDeclaration()
	 * @generated
	 */
	EAttribute getTypeDeclaration_AccessLevel();

	/**
	 * Returns the meta object for the reference list '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration#getImplements <em>Implements</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Implements</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration#getImplements()
	 * @see #getTypeDeclaration()
	 * @generated
	 */
	EReference getTypeDeclaration_Implements();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration#getMembers <em>Members</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Members</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration#getMembers()
	 * @see #getTypeDeclaration()
	 * @generated
	 */
	EReference getTypeDeclaration_Members();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Class <em>Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Class</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Class
	 * @generated
	 */
	EClass getClass_();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Class#isAbstract <em>Abstract</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Abstract</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Class#isAbstract()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_Abstract();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.Class#getSuperClass <em>Super Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Super Class</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Class#getSuperClass()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_SuperClass();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Interface <em>Interface</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Interface</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Interface
	 * @generated
	 */
	EClass getInterface();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Member <em>Member</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Member</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Member
	 * @generated
	 */
	EClass getMember();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Member#getAccess <em>Access</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Access</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Member#getAccess()
	 * @see #getMember()
	 * @generated
	 */
	EAttribute getMember_Access();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Method <em>Method</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Method</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method
	 * @generated
	 */
	EClass getMethod();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Method#isAbstract <em>Abstract</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Abstract</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#isAbstract()
	 * @see #getMethod()
	 * @generated
	 */
	EAttribute getMethod_Abstract();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Method#isStatic <em>Static</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Static</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#isStatic()
	 * @see #getMethod()
	 * @generated
	 */
	EAttribute getMethod_Static();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Method#getParams <em>Params</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Params</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#getParams()
	 * @see #getMethod()
	 * @generated
	 */
	EReference getMethod_Params();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Method#getBody <em>Body</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Body</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#getBody()
	 * @see #getMethod()
	 * @generated
	 */
	EReference getMethod_Body();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Method#call(org.tetrabox.minijava.model.miniJava.State) <em>Call</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Call</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Method#call(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getMethod__Call__State();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Method#findOverride(org.tetrabox.minijava.model.miniJava.Class) <em>Find Override</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Override</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Method#findOverride(org.tetrabox.minijava.model.miniJava.Class)
	 * @generated
	 */
	EOperation getMethod__FindOverride__Class();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Parameter <em>Parameter</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Parameter</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Parameter
	 * @generated
	 */
	EClass getParameter();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Parameter#compare(org.tetrabox.minijava.model.miniJava.Parameter) <em>Compare</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Compare</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Parameter#compare(org.tetrabox.minijava.model.miniJava.Parameter)
	 * @generated
	 */
	EOperation getParameter__Compare__Parameter();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Field <em>Field</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Field</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Field
	 * @generated
	 */
	EClass getField();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Field#getDefaultValue <em>Default Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Default Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Field#getDefaultValue()
	 * @see #getField()
	 * @generated
	 */
	EReference getField_DefaultValue();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Block <em>Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Block
	 * @generated
	 */
	EClass getBlock();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Block#getStatements <em>Statements</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Statements</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Block#getStatements()
	 * @see #getBlock()
	 * @generated
	 */
	EReference getBlock_Statements();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Block#evaluateStatementKeepContext(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement Keep Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement Keep Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Block#evaluateStatementKeepContext(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getBlock__EvaluateStatementKeepContext__State();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Block#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Block#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getBlock__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Statement <em>Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Statement
	 * @generated
	 */
	EClass getStatement();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Statement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Statement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getStatement__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.PrintStatement <em>Print Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Print Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.PrintStatement
	 * @generated
	 */
	EClass getPrintStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.PrintStatement#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.PrintStatement#getExpression()
	 * @see #getPrintStatement()
	 * @generated
	 */
	EReference getPrintStatement_Expression();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.PrintStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.PrintStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getPrintStatement__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Return <em>Return</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Return</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Return
	 * @generated
	 */
	EClass getReturn();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Return#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Return#getExpression()
	 * @see #getReturn()
	 * @generated
	 */
	EReference getReturn_Expression();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Return#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Return#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getReturn__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IfStatement <em>If Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>If Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement
	 * @generated
	 */
	EClass getIfStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.IfStatement#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#getExpression()
	 * @see #getIfStatement()
	 * @generated
	 */
	EReference getIfStatement_Expression();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.IfStatement#getThenBlock <em>Then Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Then Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#getThenBlock()
	 * @see #getIfStatement()
	 * @generated
	 */
	EReference getIfStatement_ThenBlock();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.IfStatement#getElseBlock <em>Else Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Else Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#getElseBlock()
	 * @see #getIfStatement()
	 * @generated
	 */
	EReference getIfStatement_ElseBlock();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.IfStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getIfStatement__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.WhileStatement <em>While Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>While Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement
	 * @generated
	 */
	EClass getWhileStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.WhileStatement#getCondition <em>Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Condition</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement#getCondition()
	 * @see #getWhileStatement()
	 * @generated
	 */
	EReference getWhileStatement_Condition();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.WhileStatement#getBlock <em>Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement#getBlock()
	 * @see #getWhileStatement()
	 * @generated
	 */
	EReference getWhileStatement_Block();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.WhileStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getWhileStatement__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ForStatement <em>For Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>For Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement
	 * @generated
	 */
	EClass getForStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getDeclaration <em>Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getDeclaration()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Declaration();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getCondition <em>Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Condition</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getCondition()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Condition();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getProgression <em>Progression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Progression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getProgression()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Progression();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getBlock <em>Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getBlock()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Block();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ForStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getForStatement__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.TypeRef <em>Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeRef
	 * @generated
	 */
	EClass getTypeRef();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.TypeRef#compare(org.tetrabox.minijava.model.miniJava.TypeRef) <em>Compare</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Compare</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.TypeRef#compare(org.tetrabox.minijava.model.miniJava.TypeRef)
	 * @generated
	 */
	EOperation getTypeRef__Compare__TypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SingleTypeRef <em>Single Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Single Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SingleTypeRef
	 * @generated
	 */
	EClass getSingleTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ClassRef <em>Class Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Class Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ClassRef
	 * @generated
	 */
	EClass getClassRef();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.ClassRef#getReferencedClass <em>Referenced Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Referenced Class</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ClassRef#getReferencedClass()
	 * @see #getClassRef()
	 * @generated
	 */
	EReference getClassRef_ReferencedClass();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ClassRef#compare(org.tetrabox.minijava.model.miniJava.TypeRef) <em>Compare</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Compare</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ClassRef#compare(org.tetrabox.minijava.model.miniJava.TypeRef)
	 * @generated
	 */
	EOperation getClassRef__Compare__TypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NamedElement <em>Named Element</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Named Element</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NamedElement
	 * @generated
	 */
	EClass getNamedElement();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.NamedElement#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NamedElement#getName()
	 * @see #getNamedElement()
	 * @generated
	 */
	EAttribute getNamedElement_Name();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.TypedDeclaration <em>Typed Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Typed Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypedDeclaration
	 * @generated
	 */
	EClass getTypedDeclaration();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.TypedDeclaration#getTypeRef <em>Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypedDeclaration#getTypeRef()
	 * @see #getTypedDeclaration()
	 * @generated
	 */
	EReference getTypedDeclaration_TypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Symbol <em>Symbol</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Symbol</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Symbol
	 * @generated
	 */
	EClass getSymbol();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.VariableDeclaration <em>Variable Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Variable Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.VariableDeclaration
	 * @generated
	 */
	EClass getVariableDeclaration();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Assignment <em>Assignment</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assignment</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment
	 * @generated
	 */
	EClass getAssignment();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Assignment#getAssignee <em>Assignee</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Assignee</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment#getAssignee()
	 * @see #getAssignment()
	 * @generated
	 */
	EReference getAssignment_Assignee();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Assignment#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment#getValue()
	 * @see #getAssignment()
	 * @generated
	 */
	EReference getAssignment_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Assignment#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getAssignment__EvaluateStatement__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Assignee <em>Assignee</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assignee</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignee
	 * @generated
	 */
	EClass getAssignee();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Expression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Expression
	 * @generated
	 */
	EClass getExpression();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Expression#evaluateStatement(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Statement</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Statement</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Expression#evaluateStatement(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getExpression__EvaluateStatement__State();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Expression#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Expression#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getExpression__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayTypeRef <em>Array Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayTypeRef
	 * @generated
	 */
	EClass getArrayTypeRef();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayTypeRef#getTypeRef <em>Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayTypeRef#getTypeRef()
	 * @see #getArrayTypeRef()
	 * @generated
	 */
	EReference getArrayTypeRef_TypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IntegerTypeRef <em>Integer Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Integer Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntegerTypeRef
	 * @generated
	 */
	EClass getIntegerTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.BooleanTypeRef <em>Boolean Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Boolean Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BooleanTypeRef
	 * @generated
	 */
	EClass getBooleanTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.StringTypeRef <em>String Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringTypeRef
	 * @generated
	 */
	EClass getStringTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.VoidTypeRef <em>Void Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Void Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.VoidTypeRef
	 * @generated
	 */
	EClass getVoidTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Or <em>Or</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Or</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Or
	 * @generated
	 */
	EClass getOr();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Or#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Or#getLeft()
	 * @see #getOr()
	 * @generated
	 */
	EReference getOr_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Or#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Or#getRight()
	 * @see #getOr()
	 * @generated
	 */
	EReference getOr_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Or#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Or#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getOr__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.And <em>And</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>And</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.And
	 * @generated
	 */
	EClass getAnd();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.And#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.And#getLeft()
	 * @see #getAnd()
	 * @generated
	 */
	EReference getAnd_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.And#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.And#getRight()
	 * @see #getAnd()
	 * @generated
	 */
	EReference getAnd_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.And#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.And#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getAnd__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Equality <em>Equality</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Equality</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Equality
	 * @generated
	 */
	EClass getEquality();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Equality#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Equality#getLeft()
	 * @see #getEquality()
	 * @generated
	 */
	EReference getEquality_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Equality#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Equality#getRight()
	 * @see #getEquality()
	 * @generated
	 */
	EReference getEquality_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Equality#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Equality#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getEquality__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Inequality <em>Inequality</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inequality</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality
	 * @generated
	 */
	EClass getInequality();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inequality#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality#getLeft()
	 * @see #getInequality()
	 * @generated
	 */
	EReference getInequality_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inequality#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality#getRight()
	 * @see #getInequality()
	 * @generated
	 */
	EReference getInequality_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Inequality#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getInequality__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual <em>Superior Or Equal</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Superior Or Equal</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual
	 * @generated
	 */
	EClass getSuperiorOrEqual();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getLeft()
	 * @see #getSuperiorOrEqual()
	 * @generated
	 */
	EReference getSuperiorOrEqual_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getRight()
	 * @see #getSuperiorOrEqual()
	 * @generated
	 */
	EReference getSuperiorOrEqual_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getSuperiorOrEqual__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual <em>Inferior Or Equal</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inferior Or Equal</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual
	 * @generated
	 */
	EClass getInferiorOrEqual();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getLeft()
	 * @see #getInferiorOrEqual()
	 * @generated
	 */
	EReference getInferiorOrEqual_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getRight()
	 * @see #getInferiorOrEqual()
	 * @generated
	 */
	EReference getInferiorOrEqual_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getInferiorOrEqual__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Superior <em>Superior</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Superior</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Superior
	 * @generated
	 */
	EClass getSuperior();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Superior#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Superior#getLeft()
	 * @see #getSuperior()
	 * @generated
	 */
	EReference getSuperior_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Superior#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Superior#getRight()
	 * @see #getSuperior()
	 * @generated
	 */
	EReference getSuperior_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Superior#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Superior#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getSuperior__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Inferior <em>Inferior</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inferior</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior
	 * @generated
	 */
	EClass getInferior();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inferior#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior#getLeft()
	 * @see #getInferior()
	 * @generated
	 */
	EReference getInferior_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inferior#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior#getRight()
	 * @see #getInferior()
	 * @generated
	 */
	EReference getInferior_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Inferior#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getInferior__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Plus <em>Plus</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Plus</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Plus
	 * @generated
	 */
	EClass getPlus();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Plus#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Plus#getLeft()
	 * @see #getPlus()
	 * @generated
	 */
	EReference getPlus_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Plus#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Plus#getRight()
	 * @see #getPlus()
	 * @generated
	 */
	EReference getPlus_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Plus#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Plus#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getPlus__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Minus <em>Minus</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Minus</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Minus
	 * @generated
	 */
	EClass getMinus();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Minus#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Minus#getLeft()
	 * @see #getMinus()
	 * @generated
	 */
	EReference getMinus_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Minus#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Minus#getRight()
	 * @see #getMinus()
	 * @generated
	 */
	EReference getMinus_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Minus#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Minus#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getMinus__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Multiplication <em>Multiplication</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Multiplication</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication
	 * @generated
	 */
	EClass getMultiplication();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Multiplication#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication#getLeft()
	 * @see #getMultiplication()
	 * @generated
	 */
	EReference getMultiplication_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Multiplication#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication#getRight()
	 * @see #getMultiplication()
	 * @generated
	 */
	EReference getMultiplication_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Multiplication#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getMultiplication__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Division <em>Division</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Division</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Division
	 * @generated
	 */
	EClass getDivision();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Division#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Division#getLeft()
	 * @see #getDivision()
	 * @generated
	 */
	EReference getDivision_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Division#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Division#getRight()
	 * @see #getDivision()
	 * @generated
	 */
	EReference getDivision_Right();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Division#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Division#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getDivision__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess <em>Array Access</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Access</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess
	 * @generated
	 */
	EClass getArrayAccess();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess#getObject <em>Object</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Object</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess#getObject()
	 * @see #getArrayAccess()
	 * @generated
	 */
	EReference getArrayAccess_Object();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess#getIndex <em>Index</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Index</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess#getIndex()
	 * @see #getArrayAccess()
	 * @generated
	 */
	EReference getArrayAccess_Index();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getArrayAccess__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayLength <em>Array Length</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Length</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayLength
	 * @generated
	 */
	EClass getArrayLength();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayLength#getArray <em>Array</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Array</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayLength#getArray()
	 * @see #getArrayLength()
	 * @generated
	 */
	EReference getArrayLength_Array();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ArrayLength#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayLength#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getArrayLength__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Not <em>Not</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Not</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Not
	 * @generated
	 */
	EClass getNot();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Not#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Not#getExpression()
	 * @see #getNot()
	 * @generated
	 */
	EReference getNot_Expression();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Not#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Not#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getNot__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Neg <em>Neg</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Neg</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Neg
	 * @generated
	 */
	EClass getNeg();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Neg#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Neg#getExpression()
	 * @see #getNeg()
	 * @generated
	 */
	EReference getNeg_Expression();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Neg#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Neg#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getNeg__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.FieldAccess <em>Field Access</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Field Access</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess
	 * @generated
	 */
	EClass getFieldAccess();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.FieldAccess#getReceiver <em>Receiver</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Receiver</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess#getReceiver()
	 * @see #getFieldAccess()
	 * @generated
	 */
	EReference getFieldAccess_Receiver();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.FieldAccess#getField <em>Field</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Field</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess#getField()
	 * @see #getFieldAccess()
	 * @generated
	 */
	EReference getFieldAccess_Field();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.FieldAccess#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getFieldAccess__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.MethodCall <em>Method Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Method Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall
	 * @generated
	 */
	EClass getMethodCall();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.MethodCall#getReceiver <em>Receiver</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Receiver</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#getReceiver()
	 * @see #getMethodCall()
	 * @generated
	 */
	EReference getMethodCall_Receiver();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.MethodCall#getMethod <em>Method</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Method</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#getMethod()
	 * @see #getMethodCall()
	 * @generated
	 */
	EReference getMethodCall_Method();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.MethodCall#getArgs <em>Args</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Args</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#getArgs()
	 * @see #getMethodCall()
	 * @generated
	 */
	EReference getMethodCall_Args();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.MethodCall#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getMethodCall__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.StringConstant <em>String Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Constant</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringConstant
	 * @generated
	 */
	EClass getStringConstant();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.StringConstant#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringConstant#getValue()
	 * @see #getStringConstant()
	 * @generated
	 */
	EAttribute getStringConstant_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.StringConstant#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.StringConstant#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getStringConstant__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IntConstant <em>Int Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Int Constant</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntConstant
	 * @generated
	 */
	EClass getIntConstant();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.IntConstant#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntConstant#getValue()
	 * @see #getIntConstant()
	 * @generated
	 */
	EAttribute getIntConstant_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.IntConstant#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.IntConstant#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getIntConstant__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.BoolConstant <em>Bool Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Bool Constant</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BoolConstant
	 * @generated
	 */
	EClass getBoolConstant();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.BoolConstant#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BoolConstant#getValue()
	 * @see #getBoolConstant()
	 * @generated
	 */
	EAttribute getBoolConstant_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.BoolConstant#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.BoolConstant#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getBoolConstant__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.This <em>This</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>This</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.This
	 * @generated
	 */
	EClass getThis();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.This#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.This#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getThis__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Super <em>Super</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Super</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Super
	 * @generated
	 */
	EClass getSuper();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Null <em>Null</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Null</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Null
	 * @generated
	 */
	EClass getNull();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Null#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Null#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getNull__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NewObject <em>New Object</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>New Object</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject
	 * @generated
	 */
	EClass getNewObject();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.NewObject#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Type</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject#getType()
	 * @see #getNewObject()
	 * @generated
	 */
	EReference getNewObject_Type();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.NewObject#getArgs <em>Args</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Args</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject#getArgs()
	 * @see #getNewObject()
	 * @generated
	 */
	EReference getNewObject_Args();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.NewObject#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getNewObject__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NewArray <em>New Array</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>New Array</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray
	 * @generated
	 */
	EClass getNewArray();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.NewArray#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Type</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray#getType()
	 * @see #getNewArray()
	 * @generated
	 */
	EReference getNewArray_Type();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.NewArray#getSize <em>Size</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Size</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray#getSize()
	 * @see #getNewArray()
	 * @generated
	 */
	EReference getNewArray_Size();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.NewArray#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getNewArray__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SymbolRef <em>Symbol Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Symbol Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolRef
	 * @generated
	 */
	EClass getSymbolRef();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.SymbolRef#getSymbol <em>Symbol</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Symbol</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolRef#getSymbol()
	 * @see #getSymbolRef()
	 * @generated
	 */
	EReference getSymbolRef_Symbol();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.SymbolRef#evaluateExpression(org.tetrabox.minijava.model.miniJava.State) <em>Evaluate Expression</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Evaluate Expression</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolRef#evaluateExpression(org.tetrabox.minijava.model.miniJava.State)
	 * @generated
	 */
	EOperation getSymbolRef__EvaluateExpression__State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Context <em>Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Context
	 * @generated
	 */
	EClass getContext();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Context#getBindings <em>Bindings</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Bindings</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Context#getBindings()
	 * @see #getContext()
	 * @generated
	 */
	EReference getContext_Bindings();

	/**
	 * Returns the meta object for the container reference '{@link org.tetrabox.minijava.model.miniJava.Context#getParentContext <em>Parent Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the container reference '<em>Parent Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Context#getParentContext()
	 * @see #getContext()
	 * @generated
	 */
	EReference getContext_ParentContext();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Context#getChildContext <em>Child Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Child Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Context#getChildContext()
	 * @see #getContext()
	 * @generated
	 */
	EReference getContext_ChildContext();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Context#createChildContext() <em>Create Child Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Create Child Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Context#createChildContext()
	 * @generated
	 */
	EOperation getContext__CreateChildContext();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Context#findBinding(org.tetrabox.minijava.model.miniJava.Symbol) <em>Find Binding</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Binding</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Context#findBinding(org.tetrabox.minijava.model.miniJava.Symbol)
	 * @generated
	 */
	EOperation getContext__FindBinding__Symbol();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Context#findCurrentContext() <em>Find Current Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Current Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Context#findCurrentContext()
	 * @generated
	 */
	EOperation getContext__FindCurrentContext();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Value <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Value
	 * @generated
	 */
	EClass getValue();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Value#customToString() <em>Custom To String</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Custom To String</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Value#customToString()
	 * @generated
	 */
	EOperation getValue__CustomToString();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Value#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Value#copy()
	 * @generated
	 */
	EOperation getValue__Copy();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IntegerValue <em>Integer Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Integer Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntegerValue
	 * @generated
	 */
	EClass getIntegerValue();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.IntegerValue#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntegerValue#getValue()
	 * @see #getIntegerValue()
	 * @generated
	 */
	EAttribute getIntegerValue_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.IntegerValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.IntegerValue#copy()
	 * @generated
	 */
	EOperation getIntegerValue__Copy();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.IntegerValue#customToString() <em>Custom To String</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Custom To String</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.IntegerValue#customToString()
	 * @generated
	 */
	EOperation getIntegerValue__CustomToString();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SymbolBinding <em>Symbol Binding</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Symbol Binding</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolBinding
	 * @generated
	 */
	EClass getSymbolBinding();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.SymbolBinding#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolBinding#getValue()
	 * @see #getSymbolBinding()
	 * @generated
	 */
	EReference getSymbolBinding_Value();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.SymbolBinding#getSymbol <em>Symbol</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Symbol</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolBinding#getSymbol()
	 * @see #getSymbolBinding()
	 * @generated
	 */
	EReference getSymbolBinding_Symbol();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.FieldBinding <em>Field Binding</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Field Binding</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldBinding
	 * @generated
	 */
	EClass getFieldBinding();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.FieldBinding#getField <em>Field</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Field</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldBinding#getField()
	 * @see #getFieldBinding()
	 * @generated
	 */
	EReference getFieldBinding_Field();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.FieldBinding#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldBinding#getValue()
	 * @see #getFieldBinding()
	 * @generated
	 */
	EReference getFieldBinding_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.StringValue <em>String Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringValue
	 * @generated
	 */
	EClass getStringValue();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.StringValue#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringValue#getValue()
	 * @see #getStringValue()
	 * @generated
	 */
	EAttribute getStringValue_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.StringValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.StringValue#copy()
	 * @generated
	 */
	EOperation getStringValue__Copy();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.StringValue#customToString() <em>Custom To String</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Custom To String</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.StringValue#customToString()
	 * @generated
	 */
	EOperation getStringValue__CustomToString();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.BooleanValue <em>Boolean Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Boolean Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BooleanValue
	 * @generated
	 */
	EClass getBooleanValue();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.BooleanValue#isValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BooleanValue#isValue()
	 * @see #getBooleanValue()
	 * @generated
	 */
	EAttribute getBooleanValue_Value();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.BooleanValue#customToString() <em>Custom To String</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Custom To String</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.BooleanValue#customToString()
	 * @generated
	 */
	EOperation getBooleanValue__CustomToString();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.BooleanValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.BooleanValue#copy()
	 * @generated
	 */
	EOperation getBooleanValue__Copy();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.OutputStream <em>Output Stream</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Output Stream</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.OutputStream
	 * @generated
	 */
	EClass getOutputStream();

	/**
	 * Returns the meta object for the attribute list '{@link org.tetrabox.minijava.model.miniJava.OutputStream#getStream <em>Stream</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Stream</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.OutputStream#getStream()
	 * @see #getOutputStream()
	 * @generated
	 */
	EAttribute getOutputStream_Stream();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.State <em>State</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>State</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.State
	 * @generated
	 */
	EClass getState();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.State#getRootFrame <em>Root Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Root Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.State#getRootFrame()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_RootFrame();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.State#getObjectsHeap <em>Objects Heap</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Objects Heap</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.State#getObjectsHeap()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_ObjectsHeap();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.State#getOutputStream <em>Output Stream</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Output Stream</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.State#getOutputStream()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_OutputStream();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.State#getArraysHeap <em>Arrays Heap</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Arrays Heap</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.State#getArraysHeap()
	 * @see #getState()
	 * @generated
	 */
	EReference getState_ArraysHeap();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#findCurrentFrame() <em>Find Current Frame</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Current Frame</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#findCurrentFrame()
	 * @generated
	 */
	EOperation getState__FindCurrentFrame();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#findCurrentContext() <em>Find Current Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Current Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#findCurrentContext()
	 * @generated
	 */
	EOperation getState__FindCurrentContext();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#println(java.lang.String) <em>Println</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Println</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#println(java.lang.String)
	 * @generated
	 */
	EOperation getState__Println__String();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#pushNewContext() <em>Push New Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Push New Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#pushNewContext()
	 * @generated
	 */
	EOperation getState__PushNewContext();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#popCurrentContext() <em>Pop Current Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Pop Current Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#popCurrentContext()
	 * @generated
	 */
	EOperation getState__PopCurrentContext();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#pushNewFrame(org.tetrabox.minijava.model.miniJava.ObjectInstance, org.tetrabox.minijava.model.miniJava.Call, org.tetrabox.minijava.model.miniJava.Context) <em>Push New Frame</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Push New Frame</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#pushNewFrame(org.tetrabox.minijava.model.miniJava.ObjectInstance, org.tetrabox.minijava.model.miniJava.Call, org.tetrabox.minijava.model.miniJava.Context)
	 * @generated
	 */
	EOperation getState__PushNewFrame__ObjectInstance_Call_Context();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.State#popCurrentFrame() <em>Pop Current Frame</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Pop Current Frame</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.State#popCurrentFrame()
	 * @generated
	 */
	EOperation getState__PopCurrentFrame();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Frame <em>Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame
	 * @generated
	 */
	EClass getFrame();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Frame#getCall <em>Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#getCall()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_Call();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.Frame#getInstance <em>Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#getInstance()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_Instance();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Frame#getChildFrame <em>Child Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Child Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#getChildFrame()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_ChildFrame();

	/**
	 * Returns the meta object for the container reference '{@link org.tetrabox.minijava.model.miniJava.Frame#getParentFrame <em>Parent Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the container reference '<em>Parent Frame</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#getParentFrame()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_ParentFrame();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Frame#getRootContext <em>Root Context</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Root Context</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#getRootContext()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_RootContext();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Frame#getReturnValue <em>Return Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Return Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#getReturnValue()
	 * @see #getFrame()
	 * @generated
	 */
	EReference getFrame_ReturnValue();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Frame#findCurrentFrame() <em>Find Current Frame</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Current Frame</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#findCurrentFrame()
	 * @generated
	 */
	EOperation getFrame__FindCurrentFrame();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.Frame#findCurrentContext() <em>Find Current Context</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Find Current Context</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.Frame#findCurrentContext()
	 * @generated
	 */
	EOperation getFrame__FindCurrentContext();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NullValue <em>Null Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Null Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NullValue
	 * @generated
	 */
	EClass getNullValue();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.NullValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.NullValue#copy()
	 * @generated
	 */
	EOperation getNullValue__Copy();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Call <em>Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Call
	 * @generated
	 */
	EClass getCall();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NewCall <em>New Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>New Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewCall
	 * @generated
	 */
	EClass getNewCall();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.NewCall#getNew <em>New</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>New</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewCall#getNew()
	 * @see #getNewCall()
	 * @generated
	 */
	EReference getNewCall_New();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.MethodCall2 <em>Method Call2</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Method Call2</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall2
	 * @generated
	 */
	EClass getMethodCall2();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.MethodCall2#getMethodcall <em>Methodcall</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Methodcall</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall2#getMethodcall()
	 * @see #getMethodCall2()
	 * @generated
	 */
	EReference getMethodCall2_Methodcall();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ObjectInstance <em>Object Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Object Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectInstance
	 * @generated
	 */
	EClass getObjectInstance();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.ObjectInstance#getFieldbindings <em>Fieldbindings</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Fieldbindings</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectInstance#getFieldbindings()
	 * @see #getObjectInstance()
	 * @generated
	 */
	EReference getObjectInstance_Fieldbindings();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.ObjectInstance#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Type</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectInstance#getType()
	 * @see #getObjectInstance()
	 * @generated
	 */
	EReference getObjectInstance_Type();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayInstance <em>Array Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayInstance
	 * @generated
	 */
	EClass getArrayInstance();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.ArrayInstance#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayInstance#getValue()
	 * @see #getArrayInstance()
	 * @generated
	 */
	EReference getArrayInstance_Value();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.ArrayInstance#getSize <em>Size</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Size</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayInstance#getSize()
	 * @see #getArrayInstance()
	 * @generated
	 */
	EAttribute getArrayInstance_Size();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ObjectRefValue <em>Object Ref Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Object Ref Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectRefValue
	 * @generated
	 */
	EClass getObjectRefValue();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.ObjectRefValue#getInstance <em>Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectRefValue#getInstance()
	 * @see #getObjectRefValue()
	 * @generated
	 */
	EReference getObjectRefValue_Instance();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ObjectRefValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectRefValue#copy()
	 * @generated
	 */
	EOperation getObjectRefValue__Copy();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ObjectRefValue#customToString() <em>Custom To String</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Custom To String</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ObjectRefValue#customToString()
	 * @generated
	 */
	EOperation getObjectRefValue__CustomToString();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayRefValue <em>Array Ref Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Ref Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayRefValue
	 * @generated
	 */
	EClass getArrayRefValue();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.ArrayRefValue#getInstance <em>Instance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Instance</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayRefValue#getInstance()
	 * @see #getArrayRefValue()
	 * @generated
	 */
	EReference getArrayRefValue_Instance();

	/**
	 * Returns the meta object for the '{@link org.tetrabox.minijava.model.miniJava.ArrayRefValue#copy() <em>Copy</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Copy</em>' operation.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayRefValue#copy()
	 * @generated
	 */
	EOperation getArrayRefValue__Copy();

	/**
	 * Returns the meta object for enum '{@link org.tetrabox.minijava.model.miniJava.AccessLevel <em>Access Level</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Access Level</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.AccessLevel
	 * @generated
	 */
	EEnum getAccessLevel();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	MiniJavaFactory getMiniJavaFactory();

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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ProgramImpl <em>Program</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ProgramImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getProgram()
		 * @generated
		 */
		EClass PROGRAM = eINSTANCE.getProgram();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PROGRAM__NAME = eINSTANCE.getProgram_Name();

		/**
		 * The meta object literal for the '<em><b>Imports</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROGRAM__IMPORTS = eINSTANCE.getProgram_Imports();

		/**
		 * The meta object literal for the '<em><b>Classes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROGRAM__CLASSES = eINSTANCE.getProgram_Classes();

		/**
		 * The meta object literal for the '<em><b>State</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROGRAM__STATE = eINSTANCE.getProgram_State();

		/**
		 * The meta object literal for the '<em><b>Main</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PROGRAM___MAIN = eINSTANCE.getProgram__Main();

		/**
		 * The meta object literal for the '<em><b>Initialize</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PROGRAM___INITIALIZE__ELIST = eINSTANCE.getProgram__Initialize__EList();

		/**
		 * The meta object literal for the '<em><b>Execute</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PROGRAM___EXECUTE = eINSTANCE.getProgram__Execute();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ImportImpl <em>Import</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ImportImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getImport()
		 * @generated
		 */
		EClass IMPORT = eINSTANCE.getImport();

		/**
		 * The meta object literal for the '<em><b>Imported Namespace</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute IMPORT__IMPORTED_NAMESPACE = eINSTANCE.getImport_ImportedNamespace();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl <em>Type Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeDeclaration()
		 * @generated
		 */
		EClass TYPE_DECLARATION = eINSTANCE.getTypeDeclaration();

		/**
		 * The meta object literal for the '<em><b>Access Level</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute TYPE_DECLARATION__ACCESS_LEVEL = eINSTANCE.getTypeDeclaration_AccessLevel();

		/**
		 * The meta object literal for the '<em><b>Implements</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPE_DECLARATION__IMPLEMENTS = eINSTANCE.getTypeDeclaration_Implements();

		/**
		 * The meta object literal for the '<em><b>Members</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPE_DECLARATION__MEMBERS = eINSTANCE.getTypeDeclaration_Members();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassImpl <em>Class</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ClassImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClass_()
		 * @generated
		 */
		EClass CLASS = eINSTANCE.getClass_();

		/**
		 * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__ABSTRACT = eINSTANCE.getClass_Abstract();

		/**
		 * The meta object literal for the '<em><b>Super Class</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__SUPER_CLASS = eINSTANCE.getClass_SuperClass();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl <em>Interface</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInterface()
		 * @generated
		 */
		EClass INTERFACE = eINSTANCE.getInterface();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MemberImpl <em>Member</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MemberImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMember()
		 * @generated
		 */
		EClass MEMBER = eINSTANCE.getMember();

		/**
		 * The meta object literal for the '<em><b>Access</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MEMBER__ACCESS = eINSTANCE.getMember_Access();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodImpl <em>Method</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MethodImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethod()
		 * @generated
		 */
		EClass METHOD = eINSTANCE.getMethod();

		/**
		 * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute METHOD__ABSTRACT = eINSTANCE.getMethod_Abstract();

		/**
		 * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute METHOD__STATIC = eINSTANCE.getMethod_Static();

		/**
		 * The meta object literal for the '<em><b>Params</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD__PARAMS = eINSTANCE.getMethod_Params();

		/**
		 * The meta object literal for the '<em><b>Body</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD__BODY = eINSTANCE.getMethod_Body();

		/**
		 * The meta object literal for the '<em><b>Call</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation METHOD___CALL__STATE = eINSTANCE.getMethod__Call__State();

		/**
		 * The meta object literal for the '<em><b>Find Override</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation METHOD___FIND_OVERRIDE__CLASS = eINSTANCE.getMethod__FindOverride__Class();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ParameterImpl <em>Parameter</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ParameterImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getParameter()
		 * @generated
		 */
		EClass PARAMETER = eINSTANCE.getParameter();

		/**
		 * The meta object literal for the '<em><b>Compare</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PARAMETER___COMPARE__PARAMETER = eINSTANCE.getParameter__Compare__Parameter();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldImpl <em>Field</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.FieldImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getField()
		 * @generated
		 */
		EClass FIELD = eINSTANCE.getField();

		/**
		 * The meta object literal for the '<em><b>Default Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD__DEFAULT_VALUE = eINSTANCE.getField_DefaultValue();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BlockImpl <em>Block</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BlockImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBlock()
		 * @generated
		 */
		EClass BLOCK = eINSTANCE.getBlock();

		/**
		 * The meta object literal for the '<em><b>Statements</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BLOCK__STATEMENTS = eINSTANCE.getBlock_Statements();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement Keep Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation BLOCK___EVALUATE_STATEMENT_KEEP_CONTEXT__STATE = eINSTANCE.getBlock__EvaluateStatementKeepContext__State();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation BLOCK___EVALUATE_STATEMENT__STATE = eINSTANCE.getBlock__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StatementImpl <em>Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStatement()
		 * @generated
		 */
		EClass STATEMENT = eINSTANCE.getStatement();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATEMENT___EVALUATE_STATEMENT__STATE = eINSTANCE.getStatement__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl <em>Print Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPrintStatement()
		 * @generated
		 */
		EClass PRINT_STATEMENT = eINSTANCE.getPrintStatement();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PRINT_STATEMENT__EXPRESSION = eINSTANCE.getPrintStatement_Expression();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PRINT_STATEMENT___EVALUATE_STATEMENT__STATE = eINSTANCE.getPrintStatement__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ReturnImpl <em>Return</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ReturnImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getReturn()
		 * @generated
		 */
		EClass RETURN = eINSTANCE.getReturn();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RETURN__EXPRESSION = eINSTANCE.getReturn_Expression();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation RETURN___EVALUATE_STATEMENT__STATE = eINSTANCE.getReturn__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl <em>If Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIfStatement()
		 * @generated
		 */
		EClass IF_STATEMENT = eINSTANCE.getIfStatement();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IF_STATEMENT__EXPRESSION = eINSTANCE.getIfStatement_Expression();

		/**
		 * The meta object literal for the '<em><b>Then Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IF_STATEMENT__THEN_BLOCK = eINSTANCE.getIfStatement_ThenBlock();

		/**
		 * The meta object literal for the '<em><b>Else Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IF_STATEMENT__ELSE_BLOCK = eINSTANCE.getIfStatement_ElseBlock();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation IF_STATEMENT___EVALUATE_STATEMENT__STATE = eINSTANCE.getIfStatement__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl <em>While Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getWhileStatement()
		 * @generated
		 */
		EClass WHILE_STATEMENT = eINSTANCE.getWhileStatement();

		/**
		 * The meta object literal for the '<em><b>Condition</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference WHILE_STATEMENT__CONDITION = eINSTANCE.getWhileStatement_Condition();

		/**
		 * The meta object literal for the '<em><b>Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference WHILE_STATEMENT__BLOCK = eINSTANCE.getWhileStatement_Block();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation WHILE_STATEMENT___EVALUATE_STATEMENT__STATE = eINSTANCE.getWhileStatement__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl <em>For Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getForStatement()
		 * @generated
		 */
		EClass FOR_STATEMENT = eINSTANCE.getForStatement();

		/**
		 * The meta object literal for the '<em><b>Declaration</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__DECLARATION = eINSTANCE.getForStatement_Declaration();

		/**
		 * The meta object literal for the '<em><b>Condition</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__CONDITION = eINSTANCE.getForStatement_Condition();

		/**
		 * The meta object literal for the '<em><b>Progression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__PROGRESSION = eINSTANCE.getForStatement_Progression();

		/**
		 * The meta object literal for the '<em><b>Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__BLOCK = eINSTANCE.getForStatement_Block();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation FOR_STATEMENT___EVALUATE_STATEMENT__STATE = eINSTANCE.getForStatement__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl <em>Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeRef()
		 * @generated
		 */
		EClass TYPE_REF = eINSTANCE.getTypeRef();

		/**
		 * The meta object literal for the '<em><b>Compare</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation TYPE_REF___COMPARE__TYPEREF = eINSTANCE.getTypeRef__Compare__TypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl <em>Single Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSingleTypeRef()
		 * @generated
		 */
		EClass SINGLE_TYPE_REF = eINSTANCE.getSingleTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl <em>Class Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClassRef()
		 * @generated
		 */
		EClass CLASS_REF = eINSTANCE.getClassRef();

		/**
		 * The meta object literal for the '<em><b>Referenced Class</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS_REF__REFERENCED_CLASS = eINSTANCE.getClassRef_ReferencedClass();

		/**
		 * The meta object literal for the '<em><b>Compare</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation CLASS_REF___COMPARE__TYPEREF = eINSTANCE.getClassRef__Compare__TypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl <em>Named Element</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNamedElement()
		 * @generated
		 */
		EClass NAMED_ELEMENT = eINSTANCE.getNamedElement();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute NAMED_ELEMENT__NAME = eINSTANCE.getNamedElement_Name();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl <em>Typed Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypedDeclaration()
		 * @generated
		 */
		EClass TYPED_DECLARATION = eINSTANCE.getTypedDeclaration();

		/**
		 * The meta object literal for the '<em><b>Type Ref</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPED_DECLARATION__TYPE_REF = eINSTANCE.getTypedDeclaration_TypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolImpl <em>Symbol</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbol()
		 * @generated
		 */
		EClass SYMBOL = eINSTANCE.getSymbol();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl <em>Variable Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVariableDeclaration()
		 * @generated
		 */
		EClass VARIABLE_DECLARATION = eINSTANCE.getVariableDeclaration();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl <em>Assignment</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignment()
		 * @generated
		 */
		EClass ASSIGNMENT = eINSTANCE.getAssignment();

		/**
		 * The meta object literal for the '<em><b>Assignee</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ASSIGNMENT__ASSIGNEE = eINSTANCE.getAssignment_Assignee();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ASSIGNMENT__VALUE = eINSTANCE.getAssignment_Value();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation ASSIGNMENT___EVALUATE_STATEMENT__STATE = eINSTANCE.getAssignment__EvaluateStatement__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl <em>Assignee</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignee()
		 * @generated
		 */
		EClass ASSIGNEE = eINSTANCE.getAssignee();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl <em>Expression</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getExpression()
		 * @generated
		 */
		EClass EXPRESSION = eINSTANCE.getExpression();

		/**
		 * The meta object literal for the '<em><b>Evaluate Statement</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation EXPRESSION___EVALUATE_STATEMENT__STATE = eINSTANCE.getExpression__EvaluateStatement__State();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation EXPRESSION___EVALUATE_EXPRESSION__STATE = eINSTANCE.getExpression__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl <em>Array Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayTypeRef()
		 * @generated
		 */
		EClass ARRAY_TYPE_REF = eINSTANCE.getArrayTypeRef();

		/**
		 * The meta object literal for the '<em><b>Type Ref</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_TYPE_REF__TYPE_REF = eINSTANCE.getArrayTypeRef_TypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl <em>Integer Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntegerTypeRef()
		 * @generated
		 */
		EClass INTEGER_TYPE_REF = eINSTANCE.getIntegerTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl <em>Boolean Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBooleanTypeRef()
		 * @generated
		 */
		EClass BOOLEAN_TYPE_REF = eINSTANCE.getBooleanTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl <em>String Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringTypeRef()
		 * @generated
		 */
		EClass STRING_TYPE_REF = eINSTANCE.getStringTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl <em>Void Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVoidTypeRef()
		 * @generated
		 */
		EClass VOID_TYPE_REF = eINSTANCE.getVoidTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.OrImpl <em>Or</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.OrImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getOr()
		 * @generated
		 */
		EClass OR = eINSTANCE.getOr();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OR__LEFT = eINSTANCE.getOr_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OR__RIGHT = eINSTANCE.getOr_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation OR___EVALUATE_EXPRESSION__STATE = eINSTANCE.getOr__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.AndImpl <em>And</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.AndImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAnd()
		 * @generated
		 */
		EClass AND = eINSTANCE.getAnd();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AND__LEFT = eINSTANCE.getAnd_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AND__RIGHT = eINSTANCE.getAnd_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation AND___EVALUATE_EXPRESSION__STATE = eINSTANCE.getAnd__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.EqualityImpl <em>Equality</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.EqualityImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getEquality()
		 * @generated
		 */
		EClass EQUALITY = eINSTANCE.getEquality();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EQUALITY__LEFT = eINSTANCE.getEquality_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EQUALITY__RIGHT = eINSTANCE.getEquality_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation EQUALITY___EVALUATE_EXPRESSION__STATE = eINSTANCE.getEquality__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InequalityImpl <em>Inequality</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InequalityImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInequality()
		 * @generated
		 */
		EClass INEQUALITY = eINSTANCE.getInequality();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INEQUALITY__LEFT = eINSTANCE.getInequality_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INEQUALITY__RIGHT = eINSTANCE.getInequality_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INEQUALITY___EVALUATE_EXPRESSION__STATE = eINSTANCE.getInequality__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl <em>Superior Or Equal</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperiorOrEqual()
		 * @generated
		 */
		EClass SUPERIOR_OR_EQUAL = eINSTANCE.getSuperiorOrEqual();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR_OR_EQUAL__LEFT = eINSTANCE.getSuperiorOrEqual_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR_OR_EQUAL__RIGHT = eINSTANCE.getSuperiorOrEqual_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation SUPERIOR_OR_EQUAL___EVALUATE_EXPRESSION__STATE = eINSTANCE.getSuperiorOrEqual__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl <em>Inferior Or Equal</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferiorOrEqual()
		 * @generated
		 */
		EClass INFERIOR_OR_EQUAL = eINSTANCE.getInferiorOrEqual();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR_OR_EQUAL__LEFT = eINSTANCE.getInferiorOrEqual_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR_OR_EQUAL__RIGHT = eINSTANCE.getInferiorOrEqual_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INFERIOR_OR_EQUAL___EVALUATE_EXPRESSION__STATE = eINSTANCE.getInferiorOrEqual__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl <em>Superior</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperior()
		 * @generated
		 */
		EClass SUPERIOR = eINSTANCE.getSuperior();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR__LEFT = eINSTANCE.getSuperior_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR__RIGHT = eINSTANCE.getSuperior_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation SUPERIOR___EVALUATE_EXPRESSION__STATE = eINSTANCE.getSuperior__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorImpl <em>Inferior</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferior()
		 * @generated
		 */
		EClass INFERIOR = eINSTANCE.getInferior();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR__LEFT = eINSTANCE.getInferior_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR__RIGHT = eINSTANCE.getInferior_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INFERIOR___EVALUATE_EXPRESSION__STATE = eINSTANCE.getInferior__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.PlusImpl <em>Plus</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.PlusImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPlus()
		 * @generated
		 */
		EClass PLUS = eINSTANCE.getPlus();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PLUS__LEFT = eINSTANCE.getPlus_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PLUS__RIGHT = eINSTANCE.getPlus_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PLUS___EVALUATE_EXPRESSION__STATE = eINSTANCE.getPlus__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MinusImpl <em>Minus</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MinusImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMinus()
		 * @generated
		 */
		EClass MINUS = eINSTANCE.getMinus();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MINUS__LEFT = eINSTANCE.getMinus_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MINUS__RIGHT = eINSTANCE.getMinus_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation MINUS___EVALUATE_EXPRESSION__STATE = eINSTANCE.getMinus__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl <em>Multiplication</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMultiplication()
		 * @generated
		 */
		EClass MULTIPLICATION = eINSTANCE.getMultiplication();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MULTIPLICATION__LEFT = eINSTANCE.getMultiplication_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MULTIPLICATION__RIGHT = eINSTANCE.getMultiplication_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation MULTIPLICATION___EVALUATE_EXPRESSION__STATE = eINSTANCE.getMultiplication__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.DivisionImpl <em>Division</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.DivisionImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getDivision()
		 * @generated
		 */
		EClass DIVISION = eINSTANCE.getDivision();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference DIVISION__LEFT = eINSTANCE.getDivision_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference DIVISION__RIGHT = eINSTANCE.getDivision_Right();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation DIVISION___EVALUATE_EXPRESSION__STATE = eINSTANCE.getDivision__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl <em>Array Access</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayAccess()
		 * @generated
		 */
		EClass ARRAY_ACCESS = eINSTANCE.getArrayAccess();

		/**
		 * The meta object literal for the '<em><b>Object</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_ACCESS__OBJECT = eINSTANCE.getArrayAccess_Object();

		/**
		 * The meta object literal for the '<em><b>Index</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_ACCESS__INDEX = eINSTANCE.getArrayAccess_Index();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation ARRAY_ACCESS___EVALUATE_EXPRESSION__STATE = eINSTANCE.getArrayAccess__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl <em>Array Length</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayLength()
		 * @generated
		 */
		EClass ARRAY_LENGTH = eINSTANCE.getArrayLength();

		/**
		 * The meta object literal for the '<em><b>Array</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_LENGTH__ARRAY = eINSTANCE.getArrayLength_Array();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation ARRAY_LENGTH___EVALUATE_EXPRESSION__STATE = eINSTANCE.getArrayLength__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NotImpl <em>Not</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NotImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNot()
		 * @generated
		 */
		EClass NOT = eINSTANCE.getNot();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NOT__EXPRESSION = eINSTANCE.getNot_Expression();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation NOT___EVALUATE_EXPRESSION__STATE = eINSTANCE.getNot__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NegImpl <em>Neg</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NegImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNeg()
		 * @generated
		 */
		EClass NEG = eINSTANCE.getNeg();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEG__EXPRESSION = eINSTANCE.getNeg_Expression();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation NEG___EVALUATE_EXPRESSION__STATE = eINSTANCE.getNeg__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl <em>Field Access</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFieldAccess()
		 * @generated
		 */
		EClass FIELD_ACCESS = eINSTANCE.getFieldAccess();

		/**
		 * The meta object literal for the '<em><b>Receiver</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD_ACCESS__RECEIVER = eINSTANCE.getFieldAccess_Receiver();

		/**
		 * The meta object literal for the '<em><b>Field</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD_ACCESS__FIELD = eINSTANCE.getFieldAccess_Field();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation FIELD_ACCESS___EVALUATE_EXPRESSION__STATE = eINSTANCE.getFieldAccess__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl <em>Method Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethodCall()
		 * @generated
		 */
		EClass METHOD_CALL = eINSTANCE.getMethodCall();

		/**
		 * The meta object literal for the '<em><b>Receiver</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL__RECEIVER = eINSTANCE.getMethodCall_Receiver();

		/**
		 * The meta object literal for the '<em><b>Method</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL__METHOD = eINSTANCE.getMethodCall_Method();

		/**
		 * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL__ARGS = eINSTANCE.getMethodCall_Args();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation METHOD_CALL___EVALUATE_EXPRESSION__STATE = eINSTANCE.getMethodCall__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl <em>String Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringConstant()
		 * @generated
		 */
		EClass STRING_CONSTANT = eINSTANCE.getStringConstant();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STRING_CONSTANT__VALUE = eINSTANCE.getStringConstant_Value();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STRING_CONSTANT___EVALUATE_EXPRESSION__STATE = eINSTANCE.getStringConstant__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl <em>Int Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntConstant()
		 * @generated
		 */
		EClass INT_CONSTANT = eINSTANCE.getIntConstant();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INT_CONSTANT__VALUE = eINSTANCE.getIntConstant_Value();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INT_CONSTANT___EVALUATE_EXPRESSION__STATE = eINSTANCE.getIntConstant__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl <em>Bool Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBoolConstant()
		 * @generated
		 */
		EClass BOOL_CONSTANT = eINSTANCE.getBoolConstant();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BOOL_CONSTANT__VALUE = eINSTANCE.getBoolConstant_Value();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation BOOL_CONSTANT___EVALUATE_EXPRESSION__STATE = eINSTANCE.getBoolConstant__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ThisImpl <em>This</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ThisImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getThis()
		 * @generated
		 */
		EClass THIS = eINSTANCE.getThis();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation THIS___EVALUATE_EXPRESSION__STATE = eINSTANCE.getThis__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperImpl <em>Super</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SuperImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuper()
		 * @generated
		 */
		EClass SUPER = eINSTANCE.getSuper();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NullImpl <em>Null</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NullImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNull()
		 * @generated
		 */
		EClass NULL = eINSTANCE.getNull();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation NULL___EVALUATE_EXPRESSION__STATE = eINSTANCE.getNull__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl <em>New Object</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewObject()
		 * @generated
		 */
		EClass NEW_OBJECT = eINSTANCE.getNewObject();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_OBJECT__TYPE = eINSTANCE.getNewObject_Type();

		/**
		 * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_OBJECT__ARGS = eINSTANCE.getNewObject_Args();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation NEW_OBJECT___EVALUATE_EXPRESSION__STATE = eINSTANCE.getNewObject__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl <em>New Array</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewArray()
		 * @generated
		 */
		EClass NEW_ARRAY = eINSTANCE.getNewArray();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_ARRAY__TYPE = eINSTANCE.getNewArray_Type();

		/**
		 * The meta object literal for the '<em><b>Size</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_ARRAY__SIZE = eINSTANCE.getNewArray_Size();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation NEW_ARRAY___EVALUATE_EXPRESSION__STATE = eINSTANCE.getNewArray__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl <em>Symbol Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbolRef()
		 * @generated
		 */
		EClass SYMBOL_REF = eINSTANCE.getSymbolRef();

		/**
		 * The meta object literal for the '<em><b>Symbol</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SYMBOL_REF__SYMBOL = eINSTANCE.getSymbolRef_Symbol();

		/**
		 * The meta object literal for the '<em><b>Evaluate Expression</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation SYMBOL_REF___EVALUATE_EXPRESSION__STATE = eINSTANCE.getSymbolRef__EvaluateExpression__State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ContextImpl <em>Context</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ContextImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getContext()
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
		 * The meta object literal for the '<em><b>Create Child Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation CONTEXT___CREATE_CHILD_CONTEXT = eINSTANCE.getContext__CreateChildContext();

		/**
		 * The meta object literal for the '<em><b>Find Binding</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation CONTEXT___FIND_BINDING__SYMBOL = eINSTANCE.getContext__FindBinding__Symbol();

		/**
		 * The meta object literal for the '<em><b>Find Current Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation CONTEXT___FIND_CURRENT_CONTEXT = eINSTANCE.getContext__FindCurrentContext();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ValueImpl <em>Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getValue()
		 * @generated
		 */
		EClass VALUE = eINSTANCE.getValue();

		/**
		 * The meta object literal for the '<em><b>Custom To String</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation VALUE___CUSTOM_TO_STRING = eINSTANCE.getValue__CustomToString();

		/**
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation VALUE___COPY = eINSTANCE.getValue__Copy();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntegerValueImpl <em>Integer Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IntegerValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntegerValue()
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
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INTEGER_VALUE___COPY = eINSTANCE.getIntegerValue__Copy();

		/**
		 * The meta object literal for the '<em><b>Custom To String</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INTEGER_VALUE___CUSTOM_TO_STRING = eINSTANCE.getIntegerValue__CustomToString();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolBindingImpl <em>Symbol Binding</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolBindingImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbolBinding()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldBindingImpl <em>Field Binding</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.FieldBindingImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFieldBinding()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringValueImpl <em>String Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StringValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringValue()
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
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STRING_VALUE___COPY = eINSTANCE.getStringValue__Copy();

		/**
		 * The meta object literal for the '<em><b>Custom To String</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STRING_VALUE___CUSTOM_TO_STRING = eINSTANCE.getStringValue__CustomToString();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BooleanValueImpl <em>Boolean Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BooleanValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBooleanValue()
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
		 * The meta object literal for the '<em><b>Custom To String</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation BOOLEAN_VALUE___CUSTOM_TO_STRING = eINSTANCE.getBooleanValue__CustomToString();

		/**
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation BOOLEAN_VALUE___COPY = eINSTANCE.getBooleanValue__Copy();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.OutputStreamImpl <em>Output Stream</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.OutputStreamImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getOutputStream()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StateImpl <em>State</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StateImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getState()
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
		 * The meta object literal for the '<em><b>Find Current Frame</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___FIND_CURRENT_FRAME = eINSTANCE.getState__FindCurrentFrame();

		/**
		 * The meta object literal for the '<em><b>Find Current Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___FIND_CURRENT_CONTEXT = eINSTANCE.getState__FindCurrentContext();

		/**
		 * The meta object literal for the '<em><b>Println</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___PRINTLN__STRING = eINSTANCE.getState__Println__String();

		/**
		 * The meta object literal for the '<em><b>Push New Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___PUSH_NEW_CONTEXT = eINSTANCE.getState__PushNewContext();

		/**
		 * The meta object literal for the '<em><b>Pop Current Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___POP_CURRENT_CONTEXT = eINSTANCE.getState__PopCurrentContext();

		/**
		 * The meta object literal for the '<em><b>Push New Frame</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___PUSH_NEW_FRAME__OBJECTINSTANCE_CALL_CONTEXT = eINSTANCE.getState__PushNewFrame__ObjectInstance_Call_Context();

		/**
		 * The meta object literal for the '<em><b>Pop Current Frame</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation STATE___POP_CURRENT_FRAME = eINSTANCE.getState__PopCurrentFrame();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.FrameImpl <em>Frame</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.FrameImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFrame()
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
		 * The meta object literal for the '<em><b>Find Current Frame</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation FRAME___FIND_CURRENT_FRAME = eINSTANCE.getFrame__FindCurrentFrame();

		/**
		 * The meta object literal for the '<em><b>Find Current Context</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation FRAME___FIND_CURRENT_CONTEXT = eINSTANCE.getFrame__FindCurrentContext();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NullValueImpl <em>Null Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NullValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNullValue()
		 * @generated
		 */
		EClass NULL_VALUE = eINSTANCE.getNullValue();

		/**
		 * The meta object literal for the '<em><b>Copy</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation NULL_VALUE___COPY = eINSTANCE.getNullValue__Copy();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.CallImpl <em>Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.CallImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getCall()
		 * @generated
		 */
		EClass CALL = eINSTANCE.getCall();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewCallImpl <em>New Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NewCallImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewCall()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodCall2Impl <em>Method Call2</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MethodCall2Impl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethodCall2()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ObjectInstanceImpl <em>Object Instance</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ObjectInstanceImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getObjectInstance()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayInstanceImpl <em>Array Instance</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayInstanceImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayInstance()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ObjectRefValueImpl <em>Object Ref Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ObjectRefValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getObjectRefValue()
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
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayRefValueImpl <em>Array Ref Value</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayRefValueImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayRefValue()
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

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.AccessLevel <em>Access Level</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.AccessLevel
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAccessLevel()
		 * @generated
		 */
		EEnum ACCESS_LEVEL = eINSTANCE.getAccessLevel();

	}

} //MiniJavaPackage
