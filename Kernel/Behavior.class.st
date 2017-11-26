"
My instances describe the behavior of other objects. I provide the minimum state necessary for compiling methods, and creating and running instances. Most objects are created as instances of the more fully supported subclass, Class, but I am a good starting point for providing instance-specific behavior (as in Metaclass).
"
Class {
	#name : #Behavior,
	#superclass : #Object,
	#traits : 'TBehavior',
	#classTraits : 'TBehavior classTrait',
	#instVars : [
		'superclass',
		'methodDict',
		'format',
		'layout'
	],
	#classVars : [
		'ClassProperties',
		'ObsoleteSubclasses'
	],
	#category : #Kernel-Classes
}

{ #category : #testing }
Behavior class >> canZapMethodDictionary [
	"Return false since zapping the method dictionary of Behavior class or its subclasses will cause the system to fail."
	^false
]

{ #category : #cleanup }
Behavior class >> cleanUp [
	"Flush the obsolete subclasses."

	self flushObsoleteSubclasses
]

{ #category : #'class initialization' }
Behavior class >> flushObsoleteSubclasses [
	"Behavior flushObsoleteSubclasses"
	ObsoleteSubclasses finalizeValues.
]

{ #category : #'class initialization' }
Behavior class >> initialize [
	"Behavior initialize"
	"Never called for real"
	ObsoleteSubclasses
		ifNil: [ self initializeObsoleteSubclasses ]
		ifNotNil: [ | newDict | 
			newDict := WeakKeyToCollectionDictionary newFrom: ObsoleteSubclasses.
			newDict rehash.
			ObsoleteSubclasses := newDict ].
		
	ClassProperties
		ifNil: [ self initializeClassProperties ]
		ifNotNil: [ | newDict | 
			newDict := WeakIdentityKeyDictionary newFrom: ClassProperties.
			newDict rehash.
			ClassProperties := newDict ]
]

{ #category : #'class initialization' }
Behavior class >> initializeClassProperties [
	ClassProperties := WeakIdentityKeyDictionary new.
]

{ #category : #'class initialization' }
Behavior class >> initializeObsoleteSubclasses [
	ObsoleteSubclasses := WeakKeyToCollectionDictionary new.
]

{ #category : #'reflective operations' }
Behavior >> basicIdentityHash [
	"Answer a SmallInteger whose value is related to the receiver's identity.
	 Behavior implements identityHash to allow the VM to use an object representation which
	 does not include a direct reference to an object's class in an object.  If the VM is using
	 this implementation then classes are held in a class table and instances contain the index
	 of their class in the table.  A class's class table index is its identityHash so that an instance
	 can be created without searching the table for a class's index.  The VM uses this primitive
	 to enter the class into the class table, assigning its identityHash with an as yet unused
	 class table index. If this primitive fails it means that the class table is full.  In Spur as of
	 2014 there are 22 bits of classTable index and 22 bits of identityHash per object.

	 Primitive. Essential. Do not override. See Object documentation whatIsAPrimitive."

	<primitive: 175>
	self primitiveFailed
]

{ #category : #'instance creation' }
Behavior >> basicNew [
	"Primitive. Answer an instance of the receiver (which is a class) with no 
	 indexable variables. Fail if the class is indexable. Essential. See Object 
	 documentation whatIsAPrimitive.
	
	 If the primitive fails because space is low then the scavenger will run
	 before the method is activated.  Check that space was low and retry
	 via handleFailingBasicNew if so."

	<primitive: 70 error: ec>
	ec == #'insufficient object memory' ifTrue:
		[^self handleFailingBasicNew].
	self isVariable ifTrue: [^self basicNew: 0].
	self primitiveFailed
]

{ #category : #'instance creation' }
Behavior >> basicNew: sizeRequested [
	"Primitive. Answer an instance of this class with the number of indexable
	 variables specified by the argument, sizeRequested.  Fail if this class is not
	 indexable or if the argument is not a positive Integer, or if there is not
	 enough memory available. Essential. See Object documentation whatIsAPrimitive.
	
	 If the primitive fails because space is low then the scavenger will run before the
	 method is activated.  Check args and retry via handleFailingBasicNew: if they're OK."

	<primitive: 71 error: ec>
	ec == #'insufficient object memory' ifTrue:
		[^self handleFailingBasicNew: sizeRequested].
	self isVariable ifFalse:
		[self error: self printString, ' cannot have variable sized instances'].
	self primitiveFailed
]

{ #category : #'obsolete subclasses' }
Behavior >> basicObsoleteSubclasses [
	^ObsoleteSubclasses.
]

{ #category : #'accessing instances and variables' }
Behavior >> bindingOf: varName [
	"Answer the binding of some variable resolved in the scope of the receiver"
	^self superclass bindingOf: varName
]

{ #category : #'accessing instances and variables' }
Behavior >> byteSizeOfInstance [
	"Answer the total memory size of an instance of the receiver."

	<primitive: 181 error: ec>
	self isVariable ifTrue:
		[^self byteSizeOfInstanceOfSize: 0].
	self primitiveFailed
]

{ #category : #'accessing instances and variables' }
Behavior >> byteSizeOfInstanceOfSize: basicSize [
	"Answer the total memory size of an instance of the receiver
	 with the given number of indexable instance variables."

	<primitive: 181 error: ec>
	self isVariable
		ifTrue: "If the primitive overflowed answer a close approximation"
			[(basicSize isInteger
			  and: [basicSize >= 16r1000000]) ifTrue:
				[^2 * (self byteSizeOfInstanceOfSize: basicSize + 1 // 2)
				   - (self byteSizeOfInstanceOfSize: 0)]]
		ifFalse:
			[basicSize = 0 ifTrue:
				[^self byteSizeOfInstance]].
	self primitiveFailed
]

{ #category : #'accessing instances and variables' }
Behavior >> elementSize [
	"Answer the size in bytes of an element in the receiver.  The formats are
			0	= 0 sized objects (UndefinedObject True False et al)
			1	= non-indexable objects with inst vars (Point et al)
			2	= indexable objects with no inst vars (Array et al)
			3	= indexable objects with inst vars (MethodContext AdditionalMethodState et al)
			4	= weak indexable objects with inst vars (WeakArray et al)
			5	= weak non-indexable objects with inst vars (ephemerons) (Ephemeron)
			6	= unused
			7	= immediates (SmallInteger, Character)
			8	= unused
			9	= 64-bit indexable
		10-11	= 32-bit indexable (Bitmap)
		12-15	= 16-bit indexable
		16-23	= 8-bit indexable
		24-31	= compiled methods (CompiledMethod)"
	| instSpec |
	instSpec := self instSpec.
	instSpec < 9 ifTrue: [^Smalltalk wordSize].
	instSpec >= 16 ifTrue: [^1].
	instSpec >= 12 ifTrue: [^2].
	instSpec >= 10 ifTrue: [^4].
	^8
]

{ #category : #accessing-properties }
Behavior >> ensureProperties [
	^ ClassProperties at: self ifAbsentPut: WeakKeyDictionary new
		
]

{ #category : #accessing }
Behavior >> format [
	"Answer an Integer that encodes the kinds and numbers of variables of 
	instances of the receiver."

	^format
]

{ #category : #private }
Behavior >> handleFailingBasicNew [
	"handleFailingBasicNew gets sent after basicNew has failed and allowed
	 a scavenging garbage collection to occur.  The scavenging collection
	 will have happened as the VM is activating the (failing) basicNew.  If
	 handleFailingBasicNew fails then the scavenge failed to reclaim sufficient
	 space and a global garbage collection is required.  Retry after garbage
	 collecting and growing memory if necessary.

	 Primitive. Answer an instance of this class with the number of indexable
	 variables specified by the argument, sizeRequested.  Fail if this class is not
	 indexable or if the argument is not a positive Integer, or if there is not
	 enough memory available. Essential. See Object documentation whatIsAPrimitive."

	<primitive: 70>
	Smalltalk garbageCollect < 1048576 ifTrue:
		[Smalltalk growMemoryByAtLeast: 1048576].
	^self handleFailingFailingBasicNew "retry after global garbage collect"
]

{ #category : #private }
Behavior >> handleFailingBasicNew: sizeRequested [
	"handleFailingBasicNew: gets sent after basicNew: has failed and allowed
	 a scavenging garbage collection to occur.  The scavenging collection
	 will have happened as the VM is activating the (failing) basicNew:.  If
	 handleFailingBasicNew: fails then the scavenge failed to reclaim sufficient
	 space and a global garbage collection is required.  Retry after garbage
	 collecting and growing memory if necessary.

	 Primitive. Answer an instance of this class with the number of indexable
	 variables specified by the argument, sizeRequested.  Fail if this class is not
	 indexable or if the argument is not a positive Integer, or if there is not
	 enough memory available. Essential. See Object documentation whatIsAPrimitive."

	<primitive: 71>
	| bytesRequested |
	bytesRequested := self byteSizeOfInstanceOfSize: sizeRequested.
	Smalltalk garbageCollect < bytesRequested ifTrue:
		[Smalltalk growMemoryByAtLeast: bytesRequested].
	"retry after global garbage collect and possible grow"
	^self handleFailingFailingBasicNew: sizeRequested
]

{ #category : #private }
Behavior >> handleFailingFailingBasicNew [
	"This basicNew gets sent after handleFailingBasicNew: has done a full
	 garbage collection and possibly grown memory.  If this basicNew fails
	 then the system really is low on space, so raise the OutOfMemory signal.

	 Primitive. Answer an instance of this class with the number of indexable
	 variables specified by the argument, sizeRequested.  Fail if this class is not
	 indexable or if the argument is not a positive Integer, or if there is not
	 enough memory available. Essential. See Object documentation whatIsAPrimitive."

	<primitive: 70>
	"space must be low"
	OutOfMemory signal.
	^self basicNew  "retry if user proceeds"
]

{ #category : #private }
Behavior >> handleFailingFailingBasicNew: sizeRequested [
	"This basicNew: gets sent after handleFailingBasicNew: has done a full
	 garbage collection and possibly grown memory.  If this basicNew: fails
	 then the system really is low on space, so raise the OutOfMemory signal.

	 Primitive. Answer an instance of this class with the number of indexable
	 variables specified by the argument, sizeRequested.  Fail if this class is not
	 indexable or if the argument is not a positive Integer, or if there is not
	 enough memory available. Essential. See Object documentation whatIsAPrimitive."

	<primitive: 71>
	"space must be low."
	OutOfMemory signal.
	^self basicNew: sizeRequested  "retry if user proceeds"
]

{ #category : #testing }
Behavior >> instSize [
	"Answer the number of named instance variables
	(as opposed to indexed variables) of the receiver.
	 Above Cog Spur the class format is
		<5 bits inst spec><16 bits inst size>"
	^format bitAnd: 16rFFFF
]

{ #category : #testing }
Behavior >> isBehavior [
	"Return true if the receiver is a behavior"
	^true
]

{ #category : #testing }
Behavior >> isCompiledMethodClass [
	"Answer whether the receiver has compiled method instances that mix pointers and bytes."
	^self instSpec >= 24
]

{ #category : #accessing }
Behavior >> methodDict [
       "The method dictionary of a class can be nil when we want to use the #cannotInterpret: hook. Indeed when a class dictionary is nil, the VM sends the message cannotInterpret: to the receiver but starting the look up in the superclass of the class whose method dictionary was nil.
	 Now the system relies that when the message methodDict is sent to a class a method dictionary is returned. In order to prevent the complaints of tools and IDE unaware of this feature, we fool them by providing an empty MethodDictionary. This will hopefully work in most cases, but the tools will loose the ability to modify the behaviour of this behavior. The user of #cannotInterpret: should be aware of this."

       methodDict ifNil: [^ MethodDictionary new ].
       ^ methodDict
]

{ #category : #'accessing method dictionary' }
Behavior >> methodDict: aDictionary [
	methodDict := aDictionary
]

{ #category : #accessing }
Behavior >> name [
	"Answer a String that is the name of the receiver."
	^'a subclass of ', self superclass name.
]

{ #category : #accessing-properties }
Behavior >> properties [
	^ ClassProperties at: self ifAbsent: nil
		
]

{ #category : #accessing-properties }
Behavior >> removePropertiesIfEmpty [
	^ ClassProperties at: self ifPresent: [ :dict |
		dict ifEmpty: [ ClassProperties removeKey: self ] ]
		
]

{ #category : #private }
Behavior >> setFormat: aFormatInstanceDescription [
	"only use this method with extreme care since it modifies the format of the class 
     ie a description of the number of instance variables and whether the class is
     compact, variable sized"

	format := aFormatInstanceDescription


]

{ #category : #'accessing class hierarchy' }
Behavior >> superclass [
	"Answer the receiver's superclass, a Class."

	^superclass
]

{ #category : #'accessing class hierarchy' }
Behavior >> superclass: aClass [ 
	"Change the receiver's superclass to be aClass."
	"Note: Do not use 'aClass isKindOf: Behavior' here
		in case we recompile from Behavior itself."
	(aClass isNil or: [aClass isBehavior])
		ifTrue: [superclass := aClass.
				Object flushCache]
		ifFalse: [self error: 'superclass must be a class-describing object']
]

{ #category : #traits }
Behavior >> traitComposition [
	self subclassResponsibility
]

{ #category : #traits }
Behavior >> traitComposition: aTraitComposition [
	"Compatibility purposes"
]

{ #category : #traits }
Behavior >> traitUsers [
	"Compatibility purposes"
	^IdentitySet new.
]

{ #category : #traits }
Behavior >> traitUsers: aCollection [
	"Compatibility purposes"
]

{ #category : #traits }
Behavior >> users [
	"Compatibility purposes"
	^IdentitySet new.
]

{ #category : #traits }
Behavior >> users: aCollection [
	"Compatibility purposes"
]
