"
My instances add instance-specific behavior to various class-describing objects in the system. This typically includes messages for initializing class variables and instance creation messages particular to a class. There is only one instance of a particular Metaclass, namely the class which is being described. A Metaclass shares the class variables of its instance.
	
[Subtle] In general, the superclass hierarchy for metaclasses parallels that for classes. Thus,
	Integer superclass == Number, and
	Integer class superclass == Number class.
However there is a singularity at Object. Here the class hierarchy terminates, but the metaclass hierarchy must wrap around to Class, since ALL metaclasses are subclasses of Class. Thus,
	Object superclass == nil, and
	Object class superclass == Class.

[Subtle detail] A class is know by name to an environment.  Typically this is the SystemDictionary named Smalltalk.  If we ever make lightweight classes that are not in Smalltalk, they must be in some environment.  Specifically, the code that sets 'wasPresent' in name:inEnvironment:subclassOf:instanceVariableNames:variable:words:pointers:classVariableNames:poolDictionaries:category:comment:changed: must continue to work.
"
Class {
	#name : #Metaclass,
	#superclass : #ClassDescription,
	#traits : 'TApplyingOnClassSide',
	#classTraits : 'TApplyingOnClassSide classTrait',
	#instVars : [
		'thisClass',
		'traitComposition',
		'localSelectors'
	],
	#category : #Kernel-Classes
}

{ #category : #'instance variables' }
Metaclass >> addSlot: aClassSlot [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^self theNonMetaClass addClassSlot: aClassSlot
]

{ #category : #initialize-release }
Metaclass >> adoptInstance: oldInstance from: oldMetaClass [ 
	"Recreate any existing instances of the argument, oldClass, as instances of 
	the receiver, which is a newly changed class. Permute variables as 
	necessary."
	thisClass class == self ifTrue:[^self error:'Metaclasses have only one instance'].
	oldMetaClass isMeta ifFalse:[^self error:'Argument must be Metaclass'].
	oldInstance class == oldMetaClass ifFalse:[^self error:'Not the class of argument'].
	^thisClass := self 
		newInstanceFrom: oldInstance 
		variable: self isVariable 
		size: self instSize 
		map: (self instVarMappingFrom: oldMetaClass)
]

{ #category : #'accessing parallel hierarchy' }
Metaclass >> baseClass [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^thisClass.
]

{ #category : #accessing }
Metaclass >> basicLocalSelectors [
	"Direct accessor for the instance variable localSelectors.
	Since localSelectors is lazily initialized, this may 
	return nil, which means that all selectors are local."

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^ localSelectors
]

{ #category : #accessing }
Metaclass >> basicLocalSelectors: aSetOrNil [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	localSelectors := aSetOrNil
]

{ #category : #'accessing parallel hierarchy' }
Metaclass >> classClass [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^self
]

{ #category : #fileIn/Out }
Metaclass >> definition [
	"Refer to the comment in ClassDescription|definition."

	^ String streamContents: 
		[:strm |
		strm print: self.
		self hasTraitComposition ifTrue: [
			strm
				crtab;
				nextPutAll: 'uses: ';
				print: self traitComposition ].
		
		(self usesSpecialSlot or: [ Slot showSlotClassDefinition ])
			ifFalse: [  
						strm
							crtab;
							nextPutAll: 'instanceVariableNames: ';
							store: self instanceVariablesString]
			ifTrue: [ 
						strm
							crtab;
							nextPutAll: 'slots: ';
							nextPutAll: self slotDefinitionString]]
]

{ #category : #accessing }
Metaclass >> environment [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^thisClass environment
]

{ #category : #initialize-release }
Metaclass >> instanceVariableNames: instVarString [ 
	"Declare additional named variables for my instance."
	| theClass |
	theClass := self theNonMetaClass.
	
	theClass := theClass classInstaller make: [ :builder |
		builder
			superclass: theClass superclass;
			name: theClass name;
			layoutClass: theClass classLayout class;
			slots: theClass slots;
			sharedVariablesFromString: theClass classVariablesString;
			sharedPools: theClass sharedPoolsString;
			traitComposition: theClass traitComposition;
			category: theClass category asString;
			classSlots: instVarString asSlotCollection ].
	^ theClass theMetaClass
]

{ #category : #testing }
Metaclass >> isClass [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^ true
]

{ #category : #accessing }
Metaclass >> name [
	"Answer a String that is the name of the receiver, either 'Metaclass' or 
	the name of the receiver's class followed by ' class'."

	^ thisClass isNil
		ifTrue: [ 'a Metaclass' ]
		ifFalse: [ thisClass name asString, ' class' ]
]

{ #category : #'instance creation' }
Metaclass >> new [
	"The receiver can only have one instance. Create it or complain that
	one already exists."

	thisClass class ~~ self
		ifTrue: [^thisClass := self basicNew]
		ifFalse: [self error: 'A Metaclass should only have one instance!']
]

{ #category : #'instance creation' }
Metaclass >> newAnonymousSubclass [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	^self theNonMetaClass newAnonymousSubclass class
]

{ #category : #copying }
Metaclass >> postCopy [
	"Don't share the reference to the sole instance."

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	super postCopy.
	thisClass := nil.
]

{ #category : #initialize-release }
Metaclass >> slots: slotsDefinition [ 
	"Declare additional named variables for my instance."
	| theClass |
	theClass := self theNonMetaClass.
	
	theClass := theClass classInstaller make: [ :builder |
		builder
			superclass: theClass superclass;
			name: theClass name;
			layoutClass: theClass classLayout class;
			slots: theClass slots;
			sharedVariablesFromString: theClass classVariablesString;
			sharedPools: theClass sharedPoolsString;
			traitComposition: theClass traitComposition;
			category: theClass category asString;
			classSlots: slotsDefinition].
	^ theClass theMetaClass
]

{ #category : #accessing }
Metaclass >> soleInstance [
	"The receiver has only one instance. Answer it."

	^thisClass
]

{ #category : #accessing }
Metaclass >> traitComposition [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	traitComposition ifNil: [traitComposition := TraitComposition new].
	^traitComposition
]

{ #category : #accessing }
Metaclass >> traitComposition: aTraitComposition [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	traitComposition := aTraitComposition
]

{ #category : #copying }
Metaclass >> veryDeepCopyWith: deepCopier [

	<localMetaclassMethod> 
    "This method is supposed to be local in Metaclass because of a good reason.
    We use this pragma to test if Metaclass does not contain some accidental 
    local selectors."

	"Return self.  Must be created, not copied.  Do not record me."
]
