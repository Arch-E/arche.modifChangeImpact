/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact.hibernate.vo;

/**
 * VO class that represents the allocation of a responsibility 
 * (ArchEResponsibilityVO)to a particular module (ArchEModuleVO)
 * <p>
 * This design relation is not a core concept, but rather a modifiability-specific
 * relationship that is used within the module view
 *  
 * @author Andres Diaz-Pace
 */

import edu.cmu.sei.arche.external.data.ArchEDesignRelation;
import edu.cmu.sei.arche.external.data.ArchEVersion;

public class ArchEResponsibilityToModuleRelationVO extends ArchEObjectVO 
												implements ArchEDesignRelation {

	private static final long serialVersionUID = 1L;
	
	private Integer uid;
	private String id; // TODO: To be removed

	private ArchEModuleVO parent;		  // Module	
	private ArchEResponsibilityVO child;  // Responsibility
	private String parentType;
	private String parentFact;
	private String childFact;

	public ArchEResponsibilityToModuleRelationVO() {
		super();
		this.setParentType("Module");
	}

	public ArchEResponsibilityToModuleRelationVO(ArchEVersion version) {
		super(version);
		this.setParentType("Module");
	}

	public Integer getUid() {
		return this.uid;
	}

	public void setUid(Integer uid) {
		this.uid = uid;
	}

	public String getParentType() {
		return this.parentType;
	}

	public void setParentType(String parentType) {
		this.parentType = parentType;
	}

	public String getId() {
		return this.id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public ArchEModuleVO getParent() {
		return this.parent;
	}

	public void setParent(ArchEModuleVO parent) {
		this.parent = parent;
		if(parent != null)
		this.parentFact = parent.getFactId();
	}

	public ArchEResponsibilityVO getChild() {
		return this.child;
	}

	public void setChild(ArchEResponsibilityVO child) {
		this.child = child;
		if(child != null)
			this.childFact = child.getFactId();
	}

	public String getParentFact() {
		return this.parentFact;
	}

	public void setParentFact(String parentFact) {
		this.parentFact = parentFact;
	}
	
	public String getChildFact() {
		return this.childFact;
	}

	public void setChildFact(String childFact) {
		this.childFact = childFact;
	}
	
	public String getName() {
		return ArchEResponsibilityToModuleRelationVO.class.getName();
	}

	public boolean equals(Object anotherRelation) {
		
		if (anotherRelation == null)
			return (false);
		
		Integer relationUid = ((ArchEResponsibilityToModuleRelationVO)anotherRelation).getUid();
		if (relationUid != null)
			return (relationUid.intValue() == uid.intValue());
		
		return (this == anotherRelation);
	}

}

