"
I add a number of facilities to those in ClassDescription:
	A set of all my subclasses (defined in ClassDescription, but only used here and below)
	A name by which I can be found in a SystemDictionary
	A classPool for class variables shared between this class and its metaclass
	A list of sharedPools which probably should be supplanted by some better mechanism.

My instances describe the representation and behavior of objects. I add more comprehensive programming support facilities to the basic attributes of Behavior and the descriptive facilities of ClassDescription.

The slot 'subclasses' is a redundant structure.  It is never used during execution, but is used by the development system to simplify or speed certain operations.  
"
Class {
	#name : #Class,
	#superclass : #ClassDescription,
	#traits : 'TClass',
	#classTraits : 'TClass classTrait',
	#instVars : [
		'subclasses',
		'name',
		'classPool',
		'sharedPools',
		'environment',
		'category',
		'traitComposition',
		'localSelectors'
	],
	#category : #Kernel-Classes
}

{ #category : #private }
Class >> addClassSlot: aSlot [

 	<localClassMethod> 
   "This method is supposed to be local in Class because of a good reason.
   We use this pragma to test if Class does not contain some accidental 
   local selectors."

	^self classInstaller make: [ :builder |
		builder
			superclass: self superclass;
			name: self name;
			layoutClass: self classLayout class;
			slots: self slots;
			classSlots: (self class classLayout slots copyWith: aSlot);
			sharedVariablesFromString: self classVariablesString;
			sharedPools: self sharedPoolsString;
			category: self category;
			environment: self environment].
]

{ #category : #'instance variables' }
Class >> addInstVarNamed: aString [
	"Add the argument, aString, as one of the receiver's instance variables."

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	aString substrings do: [ :each|
		self addSlot: (InstanceVariableSlot named: each asSymbol)]

]

{ #category : #'instance variables' }
Class >> addSlot: aSlot [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^self classInstaller make: [ :builder |
		builder
			superclass: self superclass;
			name: self getName;
			layoutClass: self classLayout class;
			slots: (self slots copyWith: aSlot);
			classSlots: self class classLayout slots;
			sharedVariablesFromString: self classVariablesString;
			sharedPools: self sharedPoolsString;
			category: self category;
			environment: self environment].
]

{ #category : #'accessing class hierarchy' }
Class >> addSubclass: aSubclass [ 
	"Make the argument, aSubclass, be one of the subclasses of the receiver. 
	Create an error notification if the argument's superclass is not the receiver."
	aSubclass superclass ~~ self 
		ifTrue: [^self error: aSubclass name , ' is not my subclass'].
	subclasses ifNil: [
		self subclasses: (Array with: aSubclass).
		^ self ].
	self subclasses do:[:cl| cl == aSubclass ifTrue:[^self]]. "Already my subclass"
	self subclasses: (subclasses copyWith: aSubclass).
]

{ #category : #'accessing parallel hierarchy' }
Class >> baseClass [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^ self
]

{ #category : #accessing }
Class >> basicCategory [
	^category
]

{ #category : #accessing }
Class >> basicCategory: aSymbol [
	category := aSymbol
]

{ #category : #accessing }
Class >> basicLocalSelectors [
	"Direct accessor for the instance variable localSelectors.
	Since localSelectors is lazily initialized, this may 
	return nil, which means that all selectors are local."

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^ localSelectors
]

{ #category : #accessing }
Class >> basicLocalSelectors: aSetOrNil [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	localSelectors := aSetOrNil
]

{ #category : #'accessing parallel hierarchy' }
Class >> classClass [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^self class.
]

{ #category : #accessing }
Class >> classPool [
	"Answer the dictionary of class variables."

	classPool ifNil: [ classPool := Dictionary new ].
		
	^ classPool
]

{ #category : #accessing }
Class >> classPool: aDictionary [
	classPool := aDictionary
]

{ #category : #copying }
Class >> copy [ 
	"Answer a copy of the receiver without a list of subclasses"
	| newClass |
	newClass := self class copy new
		superclass: superclass;
		methodDict: self methodDict copy;
		setFormat: format;
		setName: name;
		organization: self organization copy;
		classPool: classPool copy;
		sharedPools: sharedPools copy.
	self class instSize+1 to: self class instSize do:
		[:offset | newClass instVarAt: offset put: (self instVarAt: offset)].
	newClass classLayout: (layout copy host: newClass).
	^ newClass
]

{ #category : #accessing }
Class >> definitionForNautilus [
	"Answer a String that defines the receiver."

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	| aStream poolString |
	((self usesSpecialSlot 
		or: [ self usesSpecialClassVariables ])
		or: [ Slot showSlotClassDefinition ])
		ifTrue: [ ^ self definitionForNautilusWithSlots ].
	poolString := self sharedPoolsString.
	aStream := (String new: 800) writeStream.
	superclass
		ifNil: [ aStream nextPutAll: 'ProtoObject' ]
		ifNotNil: [ aStream nextPutAll: superclass name ].
	aStream
		nextPutAll: self kindOfSubclass;
		store: self name.
	self hasTraitComposition
		ifTrue:
			[ aStream
				cr;
				tab;
				nextPutAll: 'uses: ';
				nextPutAll: self traitCompositionString ].
	aStream
		cr;
		tab;
		nextPutAll: 'instanceVariableNames: ';
		store: self instanceVariablesString.
	aStream
		cr;
		tab;
		nextPutAll: 'classVariableNames: ';
		store: self classVariablesString.
	poolString = ''
		ifFalse:
			[ aStream
				cr;
				tab;
				nextPutAll: 'poolDictionaries: ';
				store: poolString ].
	aStream
		cr;
		tab;
		nextPutAll: 'package: ';
		store: self category asString.
	superclass
		ifNil:
			[ aStream
				nextPutAll: '.';
				cr.
			aStream nextPutAll: self name.
			aStream
				space;
				nextPutAll: 'superclass: nil' ].
	^ aStream contents
]

{ #category : #accessing }
Class >> definitionForNautilusWithSlots [
	"the class definition with a way to specify slots. Shown when the class defines special Slot
	 NOTE: this is just for testing, the final solution will evolve and be cleaner later"

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."


	| aStream poolString|

	poolString := self sharedPoolsString.

	aStream := (String new: 800) writeStream.
	superclass 
		ifNil: [aStream nextPutAll: 'ProtoObject']
		ifNotNil: [aStream nextPutAll: superclass name].
	aStream nextPutAll: ' subclass: ';
			store: self name.
	(self hasTraitComposition) ifTrue: [
		aStream cr; tab; nextPutAll: 'uses: ';
			nextPutAll: self traitCompositionString].		
			
	(self classLayout isKindOf: FixedLayout) ifFalse: [
		aStream cr; tab; nextPutAll: 'layout: ';
			nextPutAll: self classLayout class name].
	aStream cr; tab; nextPutAll: 'slots: ';
			nextPutAll: self slotDefinitionString.
	aStream cr; tab; nextPutAll: 'classVariables: ';
			nextPutAll: self classVariableDefinitionString.
	poolString = '' ifFalse: [
		aStream cr; tab; nextPutAll: 'poolDictionaries: ';
			store: poolString].
	aStream cr; tab; nextPutAll: 'category: ';
			store: self category asString.

	superclass ifNil: [ 
		aStream nextPutAll: '.'; cr.
		aStream nextPutAll: self name.
		aStream space; nextPutAll: 'superclass: nil'. ].

	^ aStream contents
]

{ #category : #organization }
Class >> environment [

	environment ifNil: [^ super environment].
	^ environment
]

{ #category : #organization }
Class >> environment: anEnvironment [

	environment := anEnvironment
]

{ #category : #private }
Class >> getName [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^ name
]

{ #category : #'accessing class hierarchy' }
Class >> hasSubclasses [
	^subclasses notNil
]

{ #category : #testing }
Class >> isClass [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^ true
]

{ #category : #accessing }
Class >> name [
	"Answer the name of the receiver."

	^ name ifNil: [ super name ]
]

{ #category : #'subclass creation' }
Class >> newAnonymousSubclass [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	^ AnonymousClassInstaller make: [ :builder |
		builder
			superclass: self ;
			layoutClass: self classLayout class ].

]

{ #category : #'subclass creation' }
Class >> private_subclass: t instanceVariableNames: f classVariableNames: d poolDictionaries: s category: cat [ 
	"This is the standard initialization message for creating a new class as a 
	subclass of an existing class (the receiver)."
	^ self classInstaller make: [ :builder |
		builder
			superclass: self;
			name: t;
			layoutClass: self classLayout class;
			slots: f asSlotCollection;
			sharedVariablesFromString: d;
			sharedPools: s;
			category: cat;
			environment: self environment;
			copyClassSlotsFromExistingClass ].

]

{ #category : #private }
Class >> setName: aSymbol [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	name := aSymbol.
]

{ #category : #'pool variables' }
Class >> sharedPools [
	"Answer an orderedCollection  of the shared pools declared in the receiver."

	^ sharedPools ifNil: [ sharedPools := OrderedCollection new ]
]

{ #category : #'pool variables' }
Class >> sharedPools: aCollection [
	sharedPools := aCollection
]

{ #category : #'accessing class hierarchy' }
Class >> subclasses [
	"Answer a Set containing the receiver's subclasses."

	^subclasses 
		ifNil: [ #() ]
		ifNotNil: [ subclasses copy ]
]

{ #category : #'accessing class hierarchy' }
Class >> subclasses: aCollection [
	subclasses := aCollection.
]

{ #category : #accessing }
Class >> traitComposition [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."

	traitComposition ifNil: [traitComposition := TraitComposition new].
	^traitComposition
]

{ #category : #accessing }
Class >> traitComposition: aTraitComposition [

	<localClassMethod> 
    "This method is supposed to be local in Class because of a good reason.
    We use this pragma to test if Class does not contain some accidental 
    local selectors."
	
	traitComposition := aTraitComposition
]
