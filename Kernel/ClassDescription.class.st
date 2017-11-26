"
I add a number of facilities to basic Behaviors:
	Named instance variables
	Category organization for methods
	The notion of a name of this class (implemented as subclass responsibility)
	The maintenance of a ChangeSet, and logging changes on a file
	Most of the mechanism for fileOut.
	
I am an abstract class, in particular, my facilities are intended for inheritance by two subclasses, Class and Metaclass.
"
Class {
	#name : #ClassDescription,
	#superclass : #Behavior,
	#traits : 'TClassDescription',
	#classTraits : 'TClassDescription classTrait',
	#instVars : [
		'instanceVariables',
		'organization'
	],
	#category : #Kernel-Classes
}

{ #category : #'accessing method dictionary' }
ClassDescription >> addAndClassifySelector: selector withMethod: compiledMethod inProtocol: category notifying: requestor [
	| priorMethodOrNil priorOriginOrNil oldProtocol newProtocol |
	
	priorMethodOrNil := self 
		compiledMethodAt: selector 
		ifAbsent: [ nil ].
	priorMethodOrNil ifNotNil: [ priorOriginOrNil := priorMethodOrNil origin ].
	
	self addSelectorSilently: selector withMethod: compiledMethod.
	
	oldProtocol := self organization categoryOfElement: selector.
	SystemAnnouncer uniqueInstance suspendAllWhile: [ 
		self organization 
			classify: selector 
			under: (category = Protocol unclassified 
				ifTrue: [ oldProtocol ]
				ifFalse: [ category ]) ].
	newProtocol := self organization categoryOfElement: selector.
	
	self isAnonymous ifTrue: [ ^ self ].
	
	(priorMethodOrNil isNil or: [ priorOriginOrNil ~= compiledMethod origin ])
		ifTrue: [ SystemAnnouncer uniqueInstance methodAdded: compiledMethod ]
		ifFalse: [ 
			"If protocol changed and someone is from different package, I need to throw a method recategorized"
			self
				notifyRepackage: selector
				method: compiledMethod
				oldProtocol: oldProtocol
				newProtocol: newProtocol.	
					
			SystemAnnouncer uniqueInstance
				methodChangedFrom: priorMethodOrNil
				to: compiledMethod
				oldProtocol: oldProtocol ]
]

{ #category : #'instance variables' }
ClassDescription >> addInstVarNamed: aString [ 
	"Add the argument, aString, as one of the receiver's instance variables."

	self subclassResponsibility
]

{ #category : #'instance variables' }
ClassDescription >> addSlot: aSlot [

	^self subclassResponsibility 
]

{ #category : #slots }
ClassDescription >> allSlots [
	^self classLayout allVisibleSlots
]

{ #category : #'accessing parallel hierarchy' }
ClassDescription >> baseClass [
	^self subclassResponsibility.
]

{ #category : #organization }
ClassDescription >> basicOrganization [
	^ organization 
]

{ #category : #organization }
ClassDescription >> basicOrganization: aClassOrg [
	organization := aClassOrg
]

{ #category : #'accessing parallel hierarchy' }
ClassDescription >> classClass [
	^self subclassResponsibility.
]

{ #category : #filein/out }
ClassDescription >> definition [
	"Answer a String that defines the receiver."

	| aStream |
	aStream := (String new: 800) writeStream.
	superclass 
		ifNil: [aStream nextPutAll: 'ProtoObject']
		ifNotNil: [aStream nextPutAll: superclass name].
	aStream nextPutAll: self kindOfSubclass;
			store: self name.
	(self hasTraitComposition) ifTrue: [
		aStream cr; tab; nextPutAll: 'uses: ';
			nextPutAll: self traitCompositionString].
	aStream cr; tab; nextPutAll: 'instanceVariableNames: ';
			store: self instanceVariablesString.
	aStream cr; tab; nextPutAll: 'classVariableNames: ';
			store: self classVariablesString.
	aStream cr; tab; nextPutAll: 'poolDictionaries: ';
			store: self sharedPoolsString.
	aStream cr; tab; nextPutAll: 'category: ';
			store: self category asString.

	superclass ifNil: [ 
		aStream nextPutAll: '.'; cr.
		aStream nextPutAll: self name.
		aStream space; nextPutAll: 'superclass: nil'. ].

	^ aStream contents
]

{ #category : #accessing }
ClassDescription >> instanceVariables [
	^self instVarNames.
]

{ #category : #'organization updating' }
ClassDescription >> noteChangesFrom: oldMethodDict [
	"create notifications about the changes made to the method dictionary"
	"additions have already been notified in #addTraitSelector:withMethod:"
		
	" deal with removal / updates relative to the old method dictionary"
	oldMethodDict keysAndValuesDo: [ :selector :oldMethod|
		self methodDict 
			at: selector
			ifPresent: [ :currentMethod|
				currentMethod == oldMethod
					ifFalse: [ self noteMethodChanged: oldMethod to: currentMethod]]
			ifAbsent: [ self noteMethodRemoved: oldMethod ]].
	
]

{ #category : #slots }
ClassDescription >> slotNamed: aName [
	^self classLayout resolveSlot: aName asSymbol
]

{ #category : #slots }
ClassDescription >> slotNamed: aName ifFound: foundBlock [
	^self slotNamed: aName ifFound: foundBlock ifNone: [ "do nothing" ]
]

{ #category : #slots }
ClassDescription >> slotNamed: aName ifFound: foundBlock ifNone: exceptionBlock [
	^self classLayout resolveSlot: aName asSymbol ifFound: foundBlock ifNone: exceptionBlock
]

{ #category : #slots }
ClassDescription >> slots [
	^self classLayout visibleSlots
]

{ #category : #'accessing parallel hierarchy' }
ClassDescription >> theMetaClass [
	^self classClass
]

{ #category : #'accessing parallel hierarchy' }
ClassDescription >> theNonMetaClass [
	^self baseClass
]

{ #category : #'organization updating' }
ClassDescription >> updateOrganizationSelector: aSymbol oldCategory: oldCategoryOrNil newCategory: newCategoryOrNil [
	| changedCategories composition |
	changedCategories := IdentitySet new.
	
	composition := self hasTraitComposition
		ifTrue: [ self traitComposition ]
		ifFalse: [ TraitComposition new ].
		
	(composition methodDescriptionsForSelector: aSymbol)
		do: [ :each | 
			self
				updateOrganizationDescription: each
				oldCategory: oldCategoryOrNil
				newCategory: newCategoryOrNil
				changedCategories: changedCategories ].
	^ changedCategories
]
