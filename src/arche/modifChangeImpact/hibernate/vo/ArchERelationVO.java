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

import java.util.Hashtable;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchERelation;
import edu.cmu.sei.arche.external.data.ArchEVersion;

public class ArchERelationVO extends ArchEObjectVO implements ArchERelation {

	private static final long serialVersionUID = 1L;
	
	protected Integer uid;
	protected String id; // TODO: to be removed
	
	protected String parentFact;
	protected String childFact;
	
	// For parameters of the form <name,value>
	protected Hashtable<String,Object> myParameters = null;

	public ArchERelationVO() {
		super();
		myParameters = new Hashtable<String,Object>();
	}
	
	public ArchERelationVO(ArchEVersion version) {
		super(version);
		myParameters = new Hashtable<String,Object>();
	}

	public Object getParent() {
		// TODO Auto-generated method stub
		return null;
	}

	public Object getChild() {
		// TODO Auto-generated method stub
		return null;
	}

	public Integer getUid() {
		return this.uid;
	}

	public void setUid(Integer uid) {
		this.uid = uid;
	}

	public String getId() {
		return this.id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public void setSource(String source){
		this.source = source;
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
	
	public String toString(){
		StringBuffer ret = new StringBuffer();
		ret.append(this.getName()+" :");
		ret.append("uid='"+uid+"'");
		ret.append(", version='"+version+"'");
		ret.append(", fact-id='"+factId+"'");
		ret.append(", source='"+source+"'");
		ret.append(", parent='"+this.getParent()+"'");
		ret.append(", child='"+this.getChild()+"'");
		return ret.toString();
	}

	public boolean equals(Object anotherRelation) {
		
		if (anotherRelation == null)
			return (false);
		
		Integer relationUid = ((ArchERelationVO)anotherRelation).getUid();
		if (relationUid != null && uid != null)
			return (relationUid.intValue() == uid.intValue());
		
		return (this == anotherRelation);
	}

	//---- Methods for manipulation of parameters ----
	
	public String getStringParameter(String propertyName) throws ArchEException {
		Object value = myParameters.get(propertyName);
		if ((value != null) && (value instanceof String))
			return ((String)value);
		else
			throw new ArchEException("No parameter[string]: "+propertyName+" available in relation: "+this.getName());
	}
	
	public boolean getBooleanParameter(String parameterName)throws ArchEException  {
		Object value = myParameters.get(parameterName);
		if ((value != null) && (value instanceof Boolean))
			return ((Boolean)value);
		else
			throw new ArchEException("No parameter[boolean]: "+parameterName+" available in relation: "+this.getName());
	}
	
	public double getDoubleParameter(String parameterName) throws ArchEException {
		Object value = myParameters.get(parameterName);
		if ((value != null) && (value instanceof Double))
			return ((Double)value);
		else
			throw new ArchEException("No parameter[double]: "+parameterName+" available in relation: "+this.getName());
	}
	
	public int getIntegerParameter(String parameterName) throws ArchEException {
		Object value = myParameters.get(parameterName);
		if ((value != null) && (value instanceof Integer))
			return ((Integer)value);
		else
			throw new ArchEException("No parameter[integer]: "+parameterName+" available in relation: "+this.getName());
	}
	
	public boolean hasParameter(String parameterName) {
		return (myParameters.containsKey(parameterName));
	}
	
	public void defineParameter(String parameterName, Object value) {
		// This method should only be invoked by the appropriate subclass of 
		// ArchECoreResponsibilityStructure or by checkRFDependencies in the reasoning framework class
		myParameters.put(parameterName, value);
		return;
	}

}
